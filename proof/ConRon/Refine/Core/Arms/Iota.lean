/-
# The ι-reduction arm of the knot (task #55, `CORE_PLAN.md` step 6)

The ι cone of `crates/con-ron-core/src/cached/core_c.rs`'s `partial_fixpoint`
block, against `ConLeche/Cached/CoreC.lean`'s `iotaRecI` (`:743-838`),
`prepareMajorI` (`:698-708`), `pinArgsI` (`:710-720`), `iotaNumArgs`
(`:722-726`), `iotaArityOk` (`:728-741`) and `iotaIndexOkI` (`:211-221`).

**The one deviation to keep in view.**  con-leche writes the whole ι step as
*one* `do` block, `iotaRecI`; the port splits it into six functions
(`iota_rec_i` → `iota_rec_rule_i` → `iota_rec_checks_i` →
`iota_rec_telescopes_i` → `iota_rec_family_i` → `iota_index_ok_i`), plus the
four pure comparand builders (`iota_cmp_levels_i`, `iota_cmp_args_i`,
`iota_params_keep_i`, `params_as_levels`) and the two allocation-free probes
the whnf spine loop asks first (`rec_arity_probe`, `iota_arity_ok`).  So five
of the theorems below have no *named* con-leche twin: their Lean side is the
corresponding **fragment of `iotaRecI`'s body**, transcribed verbatim, with
the enclosing `let`-bound variables (`c`, `cn`, `us`, `cv`, `mI`, `rP`,
`rules`, `args`, `major`, `cj`, `cjn`, `usj`, `cvj`, `rl`, `margs`) as the
theorem's arguments.  Composing the six gives `iota_rec_i_refines`, whose
statement *is* `iotaRecI` — which is what `Arms/App.lean`'s spine loop
consumes, together with `iota_arity_ok_refines`.

`prepare_major_i` is the major premise's preparation, a `Sim` against
`prepareMajorI` built from `hw.whnfSim` and the two `Arms/Major.lean`
helpers.

The `.M`-suffixed code-point tables (`iota_rec_rule_i.M`) are reached only on
the `.Err` path, which DESIGN.md §3.5 claims nothing about; they get no
theorem.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKSupport
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsCGuards

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

-- `Refine/Core/Arms/Shape.lean`'s monad plumbing, re-declared here (a `local`
-- attribute does not cross files).
attribute [local simp] StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- One `do` step of a `CheckCM` action, in the form the arms compose in: a
sub-action's `run` determines the continuation's starting state. -/
private theorem run_bind {α β : Type} {f : ConLeche.Cached.CheckCM α}
    {k : α → ConLeche.Cached.CheckCM β} {lst lst1 : ConLeche.Cached.CState}
    {v : α} (h : f.run lst = .ok (v, lst1)) :
    (f >>= k).run lst = (k v).run lst1 := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at h ⊢
  rw [h]

/-! ## The foreign helpers

Five helpers this file calls live in another agent's file (`Arms/Certs.lean`:
`def_eq_list_i`, `iota_certs_i`; `Arms/App.lean`: `pi_residual_m`;
`Arms/Major.lean`: `lit_major_to_ctor_i`, `major_to_ctor_i`).  Each is a field
below, stated in exactly the shape its own `*_refines` will have, and the
coordinator discharges the structure in `Arms/Arms.lean`. -/

/-- The five cross-file ingredients of the ι cone. -/
structure IotaDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `Arms/Certs.lean` — `def_eq_list_i` refines `defEqListI`
  (`ConLeche/Cached/CoreC.lean:201-208`). -/
  defEqList : ∀ (d : Std.U64) (xs ys : alloc.vec.Vec expr.Expr),
    ExprsWF xs → ExprsWF ys →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.def_eq_list_i mode fuel st fe d xs ys)
      (fun lfe => ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
        (absExprs xs) (absExprs ys))
  /-- `Arms/Certs.lean` — `iota_certs_i` refines `iotaCertsI`
  (`ConLeche/Cached/CoreC.lean:196-199`). -/
  iotaCerts : ∀ (d : Std.U64) (lic : Bool) (ty : expr.Expr)
      (args : alloc.vec.Vec expr.Expr), ExprWF ty → ExprsWF args →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i mode fuel st fe d lic ty args)
      (fun lfe => ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
        lic (absExpr ty) (absExprs args))
  /-- `Arms/App.lean` — `pi_residual_m` refines `piResidualM`
  (`ConLeche/Cached/StateC.lean:220-222`), the tenth `*M` wrapper: state-free,
  so a `SimP` at the `CheckCM` value. -/
  piResidual : ∀ (e : expr.Expr) (args : alloc.vec.Vec expr.Expr),
    ExprWF e → ExprsWF args →
    SimP (fun o : Option expr.Expr =>
        (pure (o.map absExpr) : ConLeche.Cached.CheckCM (Option ConLeche.Cached.ExprC)))
      (fun o => ∀ t, o = some t → ExprWF t)
      (cached.core_c.pi_residual_m e args)
      (ConLeche.Cached.piResidualM (absExpr e) (absExprs args))
  /-- `Arms/Major.lean` — `lit_major_to_ctor_i` refines `litMajorToCtorI`
  (`ConLeche/Cached/CoreC.lean:673-692`). -/
  litMajorToCtor : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.lit_major_to_ctor_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.litMajorToCtorI (knot mode lfe fuel.val) lfe
        d.val (absExpr e))
  /-- `Arms/Major.lean` — `major_to_ctor_i` refines `majorToCtorI`
  (`ConLeche/Cached/CoreC.lean:544-671`).  The cited `_recName` argument is
  unused there and dropped by the port, so it is quantified. -/
  majorToCtor : ∀ (d : Std.U64) (rn : ConLeche.Name)
      (rules : alloc.vec.Vec env.RecRule) (major : expr.Expr),
    RecRulesWF rules → ExprWF major →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.major_to_ctor_i mode fuel st fe d rules major)
      (fun lfe => ConLeche.Cached.majorToCtorI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val rn (absRecRules rules)
        (absExpr major))

/-! ## `iota_num_args` — the spine length (`core_c.rs:1763`) -/

/-- The index recursion of `iota_num_args`, on the `ExprWF` derivation (the
generated function is a `partial_fixpoint`, so there is no equation to induct
on). -/
private theorem iota_num_args_val {e : expr.Expr} (he : ExprWF e) :
    ∀ (n r : Std.U64), cached.core_c.iota_num_args e n = ok r →
      r.val = ConLeche.Cached.iotaNumArgs (absExpr e) n.val := by
  induction he with
  | @bvar i e h1 =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @fvar idx ty e hty h1 ih =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @sort u e hu h1 =>
    intro n r h
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @mk_const c us e hc hus h1 =>
    intro n r h
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @app f a e hf ha h1 ihf iha =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
    have hn1v : n1.val = n.val + 1 := by
      simpa using HashMap.uscalar_add_eq hn1
    rw [ihf n1 r h, hn1v]
    simp [ConLeche.Cached.iotaNumArgs]
  | @lam ty b m e hty hb hm h1 ihty ihb =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @forall_e ty b m e hty hb hm h1 ihty ihb =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @let_e ty v b e hty hv hb h1 ihty ihv ihb =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @lit l e hl h1 =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]
  | @proj s i x e hs hx h1 ihx =>
    intro n r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    unfold cached.core_c.iota_num_args at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Cached.iotaNumArgs]

/-- `ConLeche/Cached/CoreC.lean:722-726` — **`iota_num_args` refines
`iotaNumArgs`**: the length of an application spine, without building its
argument list (`core_c.rs:1763`). -/
theorem iota_num_args_refines {e : expr.Expr} (he : ExprWF e) (n : Std.U64) :
    SimP (fun r : Std.U64 => r.val) (fun _ => True)
      (cached.core_c.iota_num_args e n)
      (ConLeche.Cached.iotaNumArgs (absExpr e) n.val) := by
  intro r h
  exact ⟨iota_num_args_val he n r h, trivial⟩

/-! ## `rec_arity_probe` and `iota_arity_ok` — the ι step's arity pre-check
(`core_c.rs:1775`, `:1792`)

`iotaArityOk` (`ConLeche/Cached/CoreC.lean:728-741`) destructures
`fe.find? c` inline; the port's probe is that destructuring as its own
function (task #14's rule, and `core_k::rec_probe` would copy the rule list
this guard never reads), so its Lean side is the cited `match` itself. -/

/-- `ConLeche/Cached/CoreC.lean:728-741` — **`rec_arity_probe` is
`iotaArityOk`'s `some (.recInfo cv mI _ _)` destructuring**, at the two numbers
the guard reads (`core_c.rs:1775`). -/
theorem rec_arity_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe) (hc : NameWF c) :
    SimP (fun o : Option (Std.U64 × Std.Usize) => o.map (fun p => (p.1.val, p.2.val)))
      (fun _ => True)
      (cached.core_c.rec_arity_probe fe c)
      (match lfe.find? (absName c) with
       | some (.recInfo cv mI _ _) => some (mI, cv.levelParams.length)
       | _ => none) := by
  intro r h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.rec_arity_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  have hfa := FindAgree.of_rel hrel hfe
  cases ov with
  | none =>
    rw [hfa.find_none hc hov]
    simp only [Result.ok.injEq] at h
    rw [← h]; rfl
  | some ci =>
    rw [hfa.find_some hc hov]
    cases ci with
    | RecInfo cv mi rp rs =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp only [absConstantInfo, absConstantVal, Option.map_some]
      rw [alloc.vec.Vec.len_val]
      simp [absNames]
    | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | IndInfo _ _
    | CtorInfo _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h
      rw [← h]; rfl

/-- `ConLeche/Cached/CoreC.lean:728-741` — **`iota_arity_ok` refines
`iotaArityOk`**: the head is a stored recursor applied to exactly `majorIdx+1`
arguments with the recursor's own number of levels (`core_c.rs:1792`).  This is
what `Arms/App.lean`'s spine loop asks before every ι attempt. -/
theorem iota_arity_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {e : expr.Expr} (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe) (he : ExprWF e) :
    SimP id (fun _ => True) (cached.core_c.iota_arity_ok fe e)
      (ConLeche.Cached.iotaArityOk lfe (absExpr e)) := by
  intro r h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.iota_arity_ok] at h
  obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines he hf
  rw [ConLeche.Cached.iotaArityOk, ConLeche.Cached.ExprC.getAppFn_spec, ← hfabs]
  obtain ⟨⟨d, k⟩⟩ := f
  cases k with
  | Const n us =>
    obtain ⟨hn, hus⟩ := CoreK.wf_const_inv hfwf rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hp := (rec_arity_probe_refines hfe hrel hn o ho).1
    simp only [absExpr_mk, absExprKind, id_eq]
    cases hfind : lfe.find? (absName n) with
    | none =>
      rw [hfind] at hp
      simp only [Option.map_eq_none_iff] at hp
      subst hp
      simp only [Result.ok.injEq] at h
      rw [← h]
    | some ci =>
      rw [hfind] at hp
      cases ci with
      | recInfo cv mI rP rs =>
        simp only [Option.map_eq_some_iff] at hp
        obtain ⟨p, rfl, hpv⟩ := hp
        obtain ⟨mi, lp⟩ := p
        simp only [Prod.mk.injEq] at hpv
        obtain ⟨hmi, hlp⟩ := hpv
        obtain ⟨na, hna, h⟩ := bind_eq_ok_iff.mp h
        have hnav := iota_num_args_val he 0#u64 na hna
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi3v : i3.val = mi.val + 1 := by
          simpa using HashMap.uscalar_add_eq hi3
        have hnum : ConLeche.Cached.iotaNumArgs (absExpr e) 0 = na.val := by
          rw [hnav]; rfl
        split at h
        · rename_i hEq
          simp only [arc_deref_eq, bind_tc_ok, Result.ok.injEq] at h
          rw [← h, hnum, ← hmi]
          have h1 : na.val = mi.val + 1 := by rw [hEq]; exact hi3v
          simp only [h1, beq_self_eq_true, Bool.true_and, absLevels, List.length_map,
            ← hlp, id_eq]
          rw [CoreK.beq_eq_decide_eq, decide_eq_decide]
          constructor <;> intro hz <;> scalar_tac
        · rename_i hNe
          simp only [Result.ok.injEq] at h
          rw [← h, hnum, ← hmi]
          have h1 : ¬ (na.val = mi.val + 1) := by
            intro hcon
            exact hNe (by scalar_tac)
          symm
          simp only [id_eq, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          exact Or.inl h1
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _
      | ctorInfo _ _ _ | projInfo _ =>
        simp only [Option.map_eq_none_iff] at hp
        subst hp
        simp only [Result.ok.injEq] at h
        rw [← h]
  | Bvar _ | Fvar _ _ | «Sort» _ | App _ _ | Lam _ _ _ | ForallE _ _ _
  | LetE _ _ _ | Lit _ | Proj _ _ _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]
    simp only [absExpr_mk, absExprKind, id_eq]

/-! ## `is_ctor_stored_i` — `projCertI`'s stored-constructor test
(`core_c.rs:2139`) -/

/-- `ConLeche/Cached/CoreC.lean:840-848` — **`is_ctor_stored_i` is `projCertI`'s
`some (.ctorInfo _ _ _)` test**, as its own function (task #23's Aeneas error:
a borrow taken from the index and joined with a state-touching branch does not
typecheck). -/
theorem is_ctor_stored_i_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe) (hc : NameWF c) :
    SimP id (fun _ => True) (cached.core_c.is_ctor_stored_i fe c)
      (match lfe.find? (absName c) with
       | some (.ctorInfo _ _ _) => true
       | _ => false) := by
  intro r h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.is_ctor_stored_i] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  have hfa := FindAgree.of_rel hrel hfe
  cases ov with
  | none =>
    rw [hfa.find_none hc hov]
    simp only [Result.ok.injEq] at h
    rw [← h]; rfl
  | some ci =>
    rw [hfa.find_some hc hov]
    have := CoreK.is_ctor_info_refines h
    rw [id_eq, this]
    cases ci <;> rfl

/-! ## The `u64 → usize` casts

The port writes `rP as usize`, `cnP as usize` and `mI as usize` where
con-leche indexes a list with a `Nat` (`core_c.rs:1934`, `:1994`, `:2045`,
`:2057`, `:2085`, `:2113`).  Aeneas models `as usize` as
`UScalar.cast .Usize`, which **truncates** modulo `2 ^ System.Platform.numBits`
— the identity on a 64-bit target, where `Usize.max = U64.max`, and a real
truncation on a 32-bit one.  DESIGN.md §3.4's rule 3 ("`u64 → usize` casts are
avoided entirely, because their model depends on `System.Platform.numBits`") is
the rule `core_c.rs` breaks here.

`mI` and `cnP` are bounded by an argument list's length at each call site, so a
*caller* can discharge the bound; `rP` is read straight out of the stored
`recInfo` and nothing bounds it.  So each theorem below whose statement faces
an unbounded cast splits on `System.Platform.numBits_eq` and leaves the 32-bit
arm open; nothing is weakened, and the gap is one named platform fact. -/

/-- On a 64-bit target the `u64 → usize` cast is the identity. -/
private theorem cast_usize_val_64 (h : System.Platform.numBits = 64)
    (x : Std.U64) : (Std.UScalar.cast .Usize x : Std.Usize).val = x.val := by
  rw [Std.UScalar.cast_val_eq, Std.UScalarTy.Usize_numBits_eq, h]
  exact Nat.mod_eq_of_lt (by have := x.hBounds; simpa [Std.U64.size] using this)

/-! ## `params_as_levels` — `cvj.levelParams.map Level.param` (`core_c.rs:1751`)

`iotaRecI`'s canonical (`.plain`) comparand arm is
`substLevelTreesM cv.levelParams us (cvj.levelParams.map Level.param)`; §3.4
forbids closures, so the `map` is this index recursion. -/

/-- The index recursion behind `params_as_levels`. -/
private theorem params_as_levels_val {ps : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec level.Level),
      ps.val.length - i.val ≤ k → LevelsWF out →
      cached.core_c.params_as_levels ps i out = ok v →
      absLevels v
          = absLevels out
            ++ (ps.val.drop i.val).map (fun n => ConLeche.Level.param (absName n))
        ∧ LevelsWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [cached.core_c.params_as_levels.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out v hk hout h
    rw [cached.core_c.params_as_levels.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ps.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len ps by scalar_tac)] at h
      have hlt : i.val < ps.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨l1, hl1, out1, hout1, h⟩ := h
      have hl1v := Level.param_refines hl1
      have hl1w : LevelWF l1 :=
        LevelWF.param (hps _ (List.getElem_mem hlt)) hl1
      have hout1w : LevelsWF out1 := by
        intro x hx
        rw [vec_push_val hout1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hout x hx'
        · simp only [List.mem_singleton] at hx'; rw [hx']; exact hl1w
      obtain ⟨hv, hvw⟩ := ih w out1 v (by scalar_tac) hout1w h
      refine ⟨?_, hvw⟩
      rw [hv, hwv, absLevels, absLevels, vec_push_val hout1,
        List.drop_eq_getElem_cons hlt]
      simp only [hl1v, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`params_as_levels` is
`cvj.levelParams.map Level.param`** at the accumulator and cursor
(`core_c.rs:1751`). -/
theorem params_as_levels_refines {ps : alloc.vec.Vec name.Name} {i : Std.Usize}
    {out : alloc.vec.Vec level.Level} (hps : NamesWF ps) (hout : LevelsWF out) :
    SimP absLevels LevelsWF (cached.core_c.params_as_levels ps i out)
      (absLevels out ++ ((absNames ps).drop i.val).map ConLeche.Level.param) := by
  intro r h
  obtain ⟨hv, hvw⟩ := params_as_levels_val hps _ i out r le_rfl hout h
  refine ⟨?_, hvw⟩
  rw [hv, absNames, List.map_drop]
  simp [Function.comp_def]

/-! ## `pin_args_i` — the nested-rule pin instantiations (`core_c.rs:1727`)

`pinArgsI` (`ConLeche/Cached/CoreC.lean:710-720`) recurses on a `List Expr`
while the port walks the `Vec` by index into an accumulator, so the
correspondence is the suffix `pins.drop i` with `out ++` in front.  Both
`instLevelParamsM` and `instSpineM` are `pure`, so the whole thing is
state-free and the shape is `SimP` at the `CheckCM` value. -/

/-- `pinArgsI`'s `run`: `instLevelParamsM`/`instSpineM` are `pure`, so it
writes nothing and its value is the pointwise instantiation. -/
private theorem pinArgsI_run (lps : List ConLeche.Name) (us : List ConLeche.Level)
    (args : List ConLeche.Cached.ExprC) (t : Nat) :
    ∀ (ps : List ConLeche.Expr) (lst : ConLeche.Cached.CState),
      ConLeche.Cached.pinArgsI lps us args t ps lst
        = .ok (ps.map (fun p => ConLeche.Cached.ExprC.instSpine args t
            (ConLeche.Cached.ExprC.instLevelParams lps us p)), lst) := by
  intro ps
  induction ps with
  | nil => intro lst; simp [ConLeche.Cached.pinArgsI]

  | cons p ps ih =>
    intro lst
    simp [ConLeche.Cached.pinArgsI, ConLeche.Cached.instLevelParamsM,
      ConLeche.Cached.instSpineM, ih]

/-- The index recursion behind `pin_args_i`. -/
private theorem pin_args_i_val {lps : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {args pins : alloc.vec.Vec expr.Expr}
    {t : Std.U64} (hlps : NamesWF lps) (hus : LevelsWF us) (hargs : ExprsWF args)
    (hpins : ExprsWF pins) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      pins.val.length - i.val ≤ k → ExprsWF out →
      cached.core_c.pin_args_i lps us args t pins i out = ok v →
      absExprs v
          = absExprs out
            ++ (pins.val.drop i.val).map (fun p =>
                ConLeche.Cached.ExprC.instSpine (absExprs args) t.val
                  (ConLeche.Cached.ExprC.instLevelParams (absNames lps)
                    (absLevels us) (absExpr p)))
        ∧ ExprsWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [cached.core_c.pin_args_i.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len pins by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show pins.val.length ≤ i.val by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out v hk hout h
    rw [cached.core_c.pin_args_i.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ pins.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len pins by scalar_tac),
        Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show pins.val.length ≤ i.val by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len pins by scalar_tac)] at h
      have hlt : i.val < pins.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := pins.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨p1, hp1, e1, he1, out1, hout1, h⟩ := h
      rw [StateC.inst_level_params_m_eq] at hp1
      rw [StateC.inst_spine_m_eq] at he1
      obtain ⟨hp1v, hp1w⟩ :=
        ExprOpsC.inst_level_params_refines hlps hus
          (hpins _ (List.getElem_mem hlt)) hp1
      obtain ⟨he1v, he1w⟩ := ExprOpsC.inst_spine_refines hargs hp1w he1
      have hout1w : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hout x hx'
        · simp only [List.mem_singleton] at hx'; rw [hx']; exact he1w
      obtain ⟨hv, hvw⟩ := ih w out1 v (by scalar_tac) hout1w h
      refine ⟨?_, hvw⟩
      rw [hv, hwv, absExprs, absExprs, vec_push_val hout1,
        List.drop_eq_getElem_cons hlt]
      simp only [he1v, hp1v, absExprs, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- `ConLeche/Cached/CoreC.lean:710-720` — **`pin_args_i` refines `pinArgsI`**
at the accumulator and cursor (`core_c.rs:1727`). -/
theorem pin_args_i_refines {lps : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {args pins out : alloc.vec.Vec expr.Expr}
    {t : Std.U64} {i : Std.Usize} (hlps : NamesWF lps) (hus : LevelsWF us)
    (hargs : ExprsWF args) (hpins : ExprsWF pins) (hout : ExprsWF out) :
    SimP (fun r => (pure (absExprs r) :
        ConLeche.Cached.CheckCM (List ConLeche.Cached.ExprC)))
      ExprsWF
      (cached.core_c.pin_args_i lps us args t pins i out)
      (ConLeche.Cached.pinArgsI (absNames lps) (absLevels us) (absExprs args)
          t.val ((absExprs pins).drop i.val) >>=
        fun rs => pure (absExprs out ++ rs)) := by
  intro r h
  obtain ⟨hv, hvw⟩ := pin_args_i_val hlps hus hargs hpins _ i out r le_rfl hout h
  refine ⟨?_, hvw⟩
  funext lst
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, pinArgsI_run]
  rw [hv, absExprs, List.map_drop]
  simp [absExprs, Function.comp_def]

/-! ## `iota_cmp_levels_i` and `iota_cmp_args_i` — the firing comparands
(`core_c.rs:1905`, `:1924`)

`iotaRecI`'s `let cmpLvls ← match rl.fire with …` and
`let cmpArgs ← match rl.fire with …`, each as its own function.  Both are
state-free (`substLevelTreesM`, `instLevelParamsM`, `instSpineM` are all
`pure`), which is why the port may build them before the level comparison and
faithfulness is free. -/

/-- `subst_level_trees` as a pure equation (the `CheckCM` action's value). -/
private theorem subst_level_trees_val {ks : alloc.vec.Vec name.Name}
    {us ls v : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    (hls : LevelsWF ls) (h : cached.state_c.subst_level_trees ks us ls = ok v) :
    absLevels v
        = (absLevels ls).map (ConLeche.Level.subst (absNames ks) (absLevels us))
      ∧ LevelsWF v := by
  rw [cached.state_c.subst_level_trees] at h
  obtain ⟨hv, hvw⟩ :=
    StateC.subst_level_trees_from_val hks hus hls ls.val.length 0#usize _ v
      (by scalar_tac) (by intro x hx; simp [alloc.vec.Vec.new] at hx) h
  refine ⟨?_, hvw⟩
  rw [hv]
  simp [absLevels, alloc.vec.Vec.new]

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_cmp_levels_i` is
`iotaRecI`'s `cmpLvls`**: the stored level trees for a certified nested rule,
the constructor's level parameters for a canonical one (`core_c.rs:1905`). -/
theorem iota_cmp_levels_i_refines {rl : env.RecRule}
    {lps cvj_lps : alloc.vec.Vec name.Name} {us : alloc.vec.Vec level.Level}
    (hrl : RecRuleWF rl) (hlps : NamesWF lps) (hus : LevelsWF us)
    (hcvj : NamesWF cvj_lps) :
    SimP (fun r => (pure (absLevels r) :
        ConLeche.Cached.CheckCM (List ConLeche.Level)))
      LevelsWF
      (cached.core_c.iota_cmp_levels_i rl lps us cvj_lps)
      (match (absRecRule rl).fire with
       | .nested lvls _ =>
         ConLeche.Cached.substLevelTreesM (absNames lps) (absLevels us) lvls
       | _ =>
         ConLeche.Cached.substLevelTreesM (absNames lps) (absLevels us)
           ((absNames cvj_lps).map ConLeche.Level.param)) := by
  intro r h
  rw [cached.core_c.iota_cmp_levels_i] at h
  obtain ⟨-, hfw, -⟩ := hrl
  cases hfire : rl.fire with
  | Nested lvls pins =>
    rw [hfire] at h
    obtain ⟨hlvls, -⟩ : LevelsWF lvls ∧ ExprsWF pins := by
      rw [hfire] at hfw; exact hfw
    obtain ⟨hv, hvw⟩ := subst_level_trees_val hlps hus hlvls h
    refine ⟨?_, hvw⟩
    simp only [absRecRule, hfire, absFire, ConLeche.Cached.substLevelTreesM]
    rw [hv]
  | Inert =>
    rw [hfire] at h
    obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpsv, hpsw⟩ := params_as_levels_val hcvj _ 0#usize _ ps le_rfl
      (by intro x hx; simp [alloc.vec.Vec.new] at hx) hps
    obtain ⟨hv, hvw⟩ := subst_level_trees_val hlps hus hpsw h
    refine ⟨?_, hvw⟩
    simp only [absRecRule, hfire, absFire, ConLeche.Cached.substLevelTreesM]
    rw [hv, hpsv]
    simp [absLevels, absNames, alloc.vec.Vec.new, Function.comp_def]
  | Plain =>
    rw [hfire] at h
    obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpsv, hpsw⟩ := params_as_levels_val hcvj _ 0#usize _ ps le_rfl
      (by intro x hx; simp [alloc.vec.Vec.new] at hx) hps
    obtain ⟨hv, hvw⟩ := subst_level_trees_val hlps hus hpsw h
    refine ⟨?_, hvw⟩
    simp only [absRecRule, hfire, absFire, ConLeche.Cached.substLevelTreesM]
    rw [hv, hpsv]
    simp [absLevels, absNames, alloc.vec.Vec.new, Function.comp_def]

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_cmp_args_i` is `iotaRecI`'s
`cmpArgs`**: the `pinArgsI` instantiations for a nested rule, the recursor's
leading arguments for a canonical one (`core_c.rs:1924`). -/
theorem iota_cmp_args_i_refines {rl : env.RecRule} {lps : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {args : alloc.vec.Vec expr.Expr}
    {r_p : Std.U64} (hrl : RecRuleWF rl) (hlps : NamesWF lps)
    (hus : LevelsWF us) (hargs : ExprsWF args) :
    SimP (fun r => (pure (absExprs r) :
        ConLeche.Cached.CheckCM (List ConLeche.Cached.ExprC)))
      ExprsWF
      (cached.core_c.iota_cmp_args_i rl lps us args r_p)
      (match (absRecRule rl).fire with
       | .nested _ pins =>
         ConLeche.Cached.pinArgsI (absNames lps) (absLevels us)
           ((absExprs args).take r_p.val) (r_p.val - 1) pins
       | _ => pure ((absExprs args).take (absRecRule rl).ctorParams)) := by
  intro r h
  rw [cached.core_c.iota_cmp_args_i] at h
  obtain ⟨-, hfw, -⟩ := hrl
  -- sorry: on a 32-bit target `rP as usize` / `cnP as usize`
  -- (`core_c.rs:1934`, `:1944`) truncate, and the port's `take_exprs` then
  -- peels a different prefix from con-leche's `args.take rP`.  Nothing in the
  -- ι cone bounds `rP`; see the module note above.
  rcases System.Platform.numBits_eq with h32 | h64
  · sorry
  cases hfire : rl.fire with
  | Nested lvls pins =>
    rw [hfire] at h
    obtain ⟨-, hpinsw⟩ : LevelsWF lvls ∧ ExprsWF pins := by
      rw [hfire] at hfw; exact hfw
    simp only [lift_eq, bind_eq_ok_iff] at h

    obtain ⟨i0, hi0, pargs, hpargs, t1, ht1, h⟩ := h
    have hpargsv := ExprOps.take_exprs_val hpargs
    have hpargsw : ExprsWF pargs := by
      intro x hx; rw [hpargsv] at hx; exact hargs x (List.mem_of_mem_take hx)
    have ht1v := ExprOps.sub_nat_val ht1
    obtain ⟨hv, hvw⟩ :=
      pin_args_i_val hlps hus hpargsw hpinsw _ 0#usize _ r le_rfl
        (by intro x hx; simp [alloc.vec.Vec.new] at hx) h
    refine ⟨?_, hvw⟩
    funext lst
    simp only [absRecRule, hfire, absFire]
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, pinArgsI_run]
    rw [hv, absExprs, absExprs, hpargsv, ht1v, ← Result.ok_injective hi0,
      cast_usize_val_64 h64]
    simp [absExprs, alloc.vec.Vec.new, List.map_take]
  | Inert =>
    rw [hfire] at h
    simp only [lift_eq, bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, h⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [absRecRule, hfire, absFire]
      have hrv := ExprOps.take_exprs_val h
      rw [absExprs, hrv, ← Result.ok_injective hi1, cast_usize_val_64 h64]
      simp [absExprs, List.map_take]
    · intro x hx
      rw [ExprOps.take_exprs_val h] at hx
      exact hargs x (List.mem_of_mem_take hx)
  | Plain =>
    rw [hfire] at h
    simp only [lift_eq, bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, h⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [absRecRule, hfire, absFire]
      have hrv := ExprOps.take_exprs_val h
      rw [absExprs, hrv, ← Result.ok_injective hi1, cast_usize_val_64 h64]
      simp [absExprs, List.map_take]
    · intro x hx
      rw [ExprOps.take_exprs_val h] at hx
      exact hargs x (List.mem_of_mem_take hx)

/-! ## `iota_params_keep_i` — the parameter comparison's `keep`
(`core_c.rs:2013`) -/

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_params_keep_i` is the `keep`
argument of `iotaRecI`'s `certUnlessI`**: a nested rule, or a
projection-function recursor (`core_c.rs:2013`). -/
theorem iota_params_keep_i_refines {rl : env.RecRule} {c : name.Name}
    (_hrl : RecRuleWF rl) (hc : NameWF c) :
    SimP id (fun _ => True) (cached.core_c.iota_params_keep_i rl c)
      ((match (absRecRule rl).fire with | .nested _ _ => true | _ => false)
        || ConLeche.Name.isProjFnShape (absName c)) := by
  intro r h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.iota_params_keep_i] at h
  cases hfire : rl.fire with
  | Nested lvls pins =>
    rw [hfire] at h
    simp only [Result.ok.injEq] at h
    rw [id_eq, ← h]
    simp only [absRecRule, hfire, absFire]
    rfl
  | Inert =>
    rw [hfire] at h
    rw [id_eq, CoreK.name_is_proj_fn_shape_refines hc h]
    simp only [absRecRule, hfire, absFire]
    rfl
  | Plain =>
    rw [hfire] at h
    rw [id_eq, CoreK.name_is_proj_fn_shape_refines hc h]
    simp only [absRecRule, hfire, absFire]
    rfl

/-! ## `iota_index_ok_i` — the canonical-index comparison (`core_c.rs:493`) -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:211-221` — **`iota_index_ok_i` refines
`iotaIndexOkI`**: where the recursor has indices (`rP < mI`) the residual of
the constructor's telescope along the major's spine must agree, past the `cnP`
parameters, with the recursor's index arguments (`core_c.rs:493`). -/
theorem iota_index_ok_i_refines (hd : IotaDeps mode fuel)
    (d m_i r_p cn_p : Std.U64) {ty_ctor : expr.Expr}
    {margs idx : alloc.vec.Vec expr.Expr} (hty : ExprWF ty_ctor)
    (hmargs : ExprsWF margs) (hidx : ExprsWF idx) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_index_ok_i mode fuel st fe d m_i r_p cn_p
        ty_ctor margs idx)
      (fun lfe => ConLeche.Cached.iotaIndexOkI (knot mode lfe fuel.val) lfe d.val
        m_i.val r_p.val cn_p.val (absExpr ty_ctor) (absExprs margs)
        (absExprs idx)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.iota_index_ok_i at hok
  simp only [ConLeche.Cached.iotaIndexOkI]
  split at hok
  · rename_i heq
    rw [if_pos (show m_i.val = r_p.val by rw [heq])]
    simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hr, hs⟩ := hok
    cases hr; cases hs
    exact ⟨lst, by simp, hrel, hwf, trivial⟩
  · rename_i hne
    rw [if_neg (show ¬ (m_i.val = r_p.val) from fun hc => hne (by scalar_tac))]
    obtain ⟨o, ho, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hov, how⟩ := hd.piResidual ty_ctor margs hty hmargs o ho
    rw [← hov]
    cases o with
    | none =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hr, hs⟩ := hok
      cases hr; cases hs
      exact ⟨lst, by simp, hrel, hwf, trivial⟩
    | some residual =>
      have hresw : ExprWF residual := how residual rfl
      obtain ⟨sargs, hsargs, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨hsav, hsaw⟩ := ExprOps.get_app_args_refines hresw hsargs
      simp only [lift_eq, bind_eq_ok_iff] at hok
      obtain ⟨i0, hi0, rest, hrest, hok⟩ := hok
      obtain ⟨hrestv, hrestw⟩ := CoreK.drop_exprs_refines hsaw hrest
      obtain ⟨lst', hrun, hrel', hwf', -⟩ :=
        (hd.defEqList d rest idx hrestw hidx).apply hwf hfe hok hrel hfrel
      refine ⟨lst', ?_, hrel', hwf', trivial⟩
      -- sorry: on a 32-bit target `cnP as usize` (`core_c.rs:512`) truncates,
      -- so the port's `drop_exprs` drops a different prefix from con-leche's
      -- `resArgs.drop cnP`; see the module note on the `u64 → usize` casts.
      rcases System.Platform.numBits_eq with h32 | h64
      · sorry
      have hi0v : i0.val = cn_p.val := by
        rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 cn_p
      simp only [Option.map_some]
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure]
      rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← hsav, ← hi0v, ← hrestv]
      simpa using hrun

/-! ## `iota_rec_family_i` — the ONE certificate family (`core_c.rs:2075`)

`iotaRecI`'s `certAtI mode (do let tyRec ← constTyAtM …; …)` argument: the
recursor's telescope against the non-major prefix plus the prepared major, the
constructor's telescope against the major's spine, and the canonical-index
comparison.  Both telescope runs are licensed off `mode.betaGate`, the same
function the β site reads. -/

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_rec_family_i` is
`iotaRecI`'s certificate family** (`core_c.rs:2075`). -/
theorem iota_rec_family_i_refines (hd : IotaDeps mode fuel)
    (d : Std.U64) {c cj : name.Name} (m_i r_p : Std.U64) {rl : env.RecRule}
    {us usj : alloc.vec.Vec level.Level} {args margs : alloc.vec.Vec expr.Expr}
    {major : expr.Expr} (hc : NameWF c) (hcj : NameWF cj)
    (hus : LevelsWF us) (husj : LevelsWF usj) (hargs : ExprsWF args)
    (hmargs : ExprsWF margs) (hmajor : ExprWF major) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_rec_family_i mode fuel st fe d c cj m_i r_p
        rl us usj args margs major)
      (fun lfe => do
        let tyRec ← ConLeche.Cached.constTyAtM lfe (absName c) (absName c)
          (absLevels us)
        if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
            (absMode mode).betaGate tyRec
            ((absExprs args).take m_i.val ++ [absExpr major]) then do
          let tyCtor ← ConLeche.Cached.constTyAtM lfe (absName cj) (absName cj)
            (absLevels usj)
          if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
              (absMode mode).betaGate tyCtor (absExprs margs) then
            ConLeche.Cached.iotaIndexOkI (knot mode lfe fuel.val) lfe d.val
              m_i.val r_p.val (absRecRule rl).ctorParams tyCtor (absExprs margs)
              (((absExprs args).take m_i.val).drop r_p.val)
          else pure false
        else pure false) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  -- sorry: on a 32-bit target `mI as usize` (`core_c.rs:2084`) and
  -- `rP as usize` (`core_c.rs:2113`) truncate, so the port's `take_exprs` /
  -- `drop_exprs` peel different prefixes from con-leche's `args.take mI` and
  -- `(args.take mI).drop rP`; see the module note on the `u64 → usize` casts.
  rcases System.Platform.numBits_eq with h32 | h64
  · sorry
  simp only []
  unfold cached.core_c.iota_rec_family_i at hok
  obtain ⟨lic, hlic, hok⟩ := bind_eq_ok_iff.mp hok
  have hlicv := Env.beta_gate_refines hlic
  rw [lift_eq] at hok
  obtain ⟨i0, hi0, hok⟩ := bind_eq_ok_iff.mp hok
  have hi0v : i0.val = m_i.val := by
    rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 m_i
  obtain ⟨pre, hpre, hok⟩ := bind_eq_ok_iff.mp hok
  have hprev : absExprs pre = (absExprs args).take m_i.val := by
    rw [absExprs, ExprOps.take_exprs_val hpre, hi0v, absExprs, List.map_take]
  have hprew : ExprsWF pre := by
    intro x hx
    rw [ExprOps.take_exprs_val hpre] at hx
    exact hargs x (List.mem_of_mem_take hx)
  obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨rr, st1⟩ := p1
  cases rr with
  | Err err => simp at hok
  | Ok rty =>
  obtain ⟨lst1, hrun1, hrel1, hwf1, htyw⟩ :=
    StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hc hus hp1
      lst lfe hrel hfrel (absName c)
  obtain ⟨v, hv, hok⟩ := bind_eq_ok_iff.mp hok
  have hvv : v = pre := Env.exprs_copy_refines hv
  subst hvv
  obtain ⟨v1, hv1, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hv1v, hv1w⟩ := CoreK.expr_singleton_refines hmajor hv1
  obtain ⟨rspine, hrspine, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hrsv, hrsw⟩ := CoreK.append_exprs_refines hprew hv1w hrspine
  rw [hprev, hv1v] at hrsv
  obtain ⟨p2, hp2, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨rr1, st2⟩ := p2
  cases rr1 with
  | Err err => simp at hok
  | Ok b =>
  obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
    (hd.iotaCerts d lic rty rspine htyw hrsw).apply hwf1 hfe hp2 hrel1 hfrel
  rw [hlicv, hrsv] at hrun2
  cases b with
  | true =>
    obtain ⟨p3, hp3, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨rr2, st3⟩ := p3
    cases rr2 with
    | Err err => simp at hok
    | Ok cty =>
    obtain ⟨lst3, hrun3, hrel3, hwf3, hctyw⟩ :=
      StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf2 hfe hcj husj
        hp3 lst2 lfe hrel2 hfrel (absName cj)
    obtain ⟨p4, hp4, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨rr3, st4⟩ := p4
    cases rr3 with
    | Err err => simp at hok
    | Ok b1 =>
    obtain ⟨lst4, hrun4, hrel4, hwf4, -⟩ :=
      (hd.iotaCerts d lic cty margs hctyw hmargs).apply hwf3 hfe hp4 hrel3 hfrel
    rw [hlicv] at hrun4
    cases b1 with
    | true =>
      rw [lift_eq] at hok
      obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
      have hi1v : i1.val = r_p.val := by
        rw [← Result.ok_injective hi1]; exact cast_usize_val_64 h64 r_p
      obtain ⟨idx, hidx, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨hidxv, hidxw⟩ := CoreK.drop_exprs_refines hprew hidx
      rw [hprev, hi1v] at hidxv
      obtain ⟨lst5, hrun5, hrel5, hwf5, -⟩ :=
        (iota_index_ok_i_refines hd d m_i r_p rl.ctor_params hctyw hmargs
          hidxw).apply hwf4 hfe hok hrel4 hfrel
      rw [hidxv] at hrun5
      refine ⟨lst5, ?_, hrel5, hwf5, trivial⟩
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure] at hrun1 hrun2 hrun3 hrun4 hrun5 ⊢
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, id_eq, ↓reduceIte]
      simpa [absRecRule] using hrun5
    | false =>
      have hok' : (ok (core.result.Result.Ok false, st4) :
          Result ((core.result.Result Bool core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      refine ⟨lst4, ?_, hrel4, hwf4, trivial⟩
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure] at hrun1 hrun2 hrun3 hrun4 ⊢
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, id_eq, ↓reduceIte]
      simp
  | false =>
    have hok' : (ok (core.result.Result.Ok false, st2) :
        Result ((core.result.Result Bool core_types.CheckError) ×
          cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
    simp only [Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at hok'
    obtain ⟨hr, hs⟩ := hok'
    cases hr; cases hs
    refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at hrun1 hrun2 ⊢
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, id_eq, ↓reduceIte]
    simp

/-! ## `iota_rec_telescopes_i` — the family under `certAtI`, then the reduct
(`core_c.rs:2029`)

`iotaRecI`'s `if ← certAtI mode (…) then do let rhs ← ruleRhsAtM …; let red ←
mkAppNM …; pure (some red) else pure none`. -/

/-- The reduct branch, shared by the two modes: `ruleRhsAtM` then `mkAppNM`. -/
private theorem telescopes_tail {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    {c cj : name.Name} (r_p : Std.U64) {rl : env.RecRule}
    {us : alloc.vec.Vec level.Level} {args margs : alloc.vec.Vec expr.Expr}
    (hc : NameWF c) (hcj : NameWF cj) (hus : LevelsWF us) (hargs : ExprsWF args)
    (hmargs : ExprsWF margs) (h64 : System.Platform.numBits = 64)
    {stA : cached.state_c.CState} {lstA : ConLeche.Cached.CState}
    {r : Option expr.Expr} {st' : cached.state_c.CState}
    (hrelA : StateRel stA lstA) (hwfA : StateWF stA)
    (hok : (do
        let (r0, st2) ← cached.state_c.rule_rhs_at_m stA fe c cj us
        match r0 with
        | .Ok rhs =>
          let i ← lift (Std.UScalar.cast .Usize rl.ctor_params)
          let fields ← kernel.core_k.drop_exprs margs i
          let i1 ← lift (Std.UScalar.cast .Usize r_p)
          let v ← kernel.expr_ops.take_exprs args i1
          let spine ← kernel.core_k.append_exprs v fields
          let e ← cached.state_c.mk_app_n_m rhs spine
          ok (core.result.Result.Ok (some e), st2)
        | .Err err => ok (core.result.Result.Err err, st2)) =
      ok (core.result.Result.Ok r, st')) :
    ∃ lst', (do
        let rhs ← ConLeche.Cached.ruleRhsAtM lfe (absName c) (absName cj)
          (absName c) (absName cj) (absLevels us)
        let red ← ConLeche.Cached.mkAppNM rhs
          ((absExprs args).take r_p.val
            ++ (absExprs margs).drop (absRecRule rl).ctorParams)
        pure (some red)).run lstA = .ok (Option.map absExpr r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' ∧ (∀ t, r = some t → ExprWF t) := by
  obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨r0, st2⟩ := p
  cases r0 with
  | Err err => simp at hok
  | Ok rhs =>
  obtain ⟨lst2, hrunR, hrel2, hwf2, hrhsw⟩ :=
    StateC.rule_rhs_at_m_refines StateC.instLevelParamsRefines hwfA hfe hc hcj hus
      hp lstA lfe hrelA hfrel (absName c) (absName cj)
  rw [lift_eq] at hok
  obtain ⟨i0, hi0, hok⟩ := bind_eq_ok_iff.mp hok
  have hi0v : i0.val = rl.ctor_params.val := by
    rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
  obtain ⟨fields, hfields, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hfv, hfw⟩ := CoreK.drop_exprs_refines hmargs hfields
  rw [hi0v] at hfv
  rw [lift_eq] at hok
  obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
  have hi1v : i1.val = r_p.val := by
    rw [← Result.ok_injective hi1]; exact cast_usize_val_64 h64 _
  obtain ⟨v, hv, hok⟩ := bind_eq_ok_iff.mp hok
  have hvv : absExprs v = (absExprs args).take r_p.val := by
    rw [absExprs, ExprOps.take_exprs_val hv, hi1v, absExprs, List.map_take]
  have hvw : ExprsWF v := by
    intro x hx
    rw [ExprOps.take_exprs_val hv] at hx
    exact hargs x (List.mem_of_mem_take hx)
  obtain ⟨spine, hspine, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hsv, hsw⟩ := CoreK.append_exprs_refines hvw hfw hspine
  rw [hvv, hfv] at hsv
  obtain ⟨e, he, hok⟩ := bind_eq_ok_iff.mp hok
  rw [StateC.mk_app_n_m_eq] at he
  obtain ⟨hev, hew⟩ := ExprOpsC.mk_app_n_refines hrhsw hsw he
  rw [hsv] at hev
  have hok' : (ok (core.result.Result.Ok (some e), st2) :
      Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
        cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
  obtain ⟨hr, hs⟩ := hok'
  cases hr; cases hs
  refine ⟨lst2, ?_, hrel2, hwf2, ?_⟩
  · simp only [StateT.run] at hrunR
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrunR, ConLeche.Cached.mkAppNM, absRecRule]
    simp [hev]
  · intro t ht
    simp only [Option.some.injEq] at ht
    rw [← ht]; exact hew

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_rec_telescopes_i` is
`iotaRecI`'s `certAtI` block and the reduct it licenses** (`core_c.rs:2029`). -/
theorem iota_rec_telescopes_i_refines (hd : IotaDeps mode fuel) (d : Std.U64)
    {c cj : name.Name} (m_i r_p : Std.U64) {rl : env.RecRule}
    {us usj : alloc.vec.Vec level.Level} {args margs : alloc.vec.Vec expr.Expr}
    {major : expr.Expr} (hc : NameWF c) (hcj : NameWF cj)
    (hus : LevelsWF us) (husj : LevelsWF usj) (hargs : ExprsWF args)
    (hmargs : ExprsWF margs) (hmajor : ExprWF major) :
    Sim (Option.map absExpr) (fun o => ∀ t, o = some t → ExprWF t)
      (fun st fe => cached.core_c.iota_rec_telescopes_i mode fuel st fe d c cj m_i
        r_p rl us usj args margs major)
      (fun lfe => do
        if ← ConLeche.Cached.certAtI (absMode mode) (do
            let tyRec ← ConLeche.Cached.constTyAtM lfe (absName c) (absName c)
              (absLevels us)
            if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                (absMode mode).betaGate tyRec
                ((absExprs args).take m_i.val ++ [absExpr major]) then do
              let tyCtor ← ConLeche.Cached.constTyAtM lfe (absName cj) (absName cj)
                (absLevels usj)
              if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                  (absMode mode).betaGate tyCtor (absExprs margs) then
                ConLeche.Cached.iotaIndexOkI (knot mode lfe fuel.val) lfe d.val
                  m_i.val r_p.val (absRecRule rl).ctorParams tyCtor
                  (absExprs margs) (((absExprs args).take m_i.val).drop r_p.val)
              else pure false
            else pure false) then do
          let rhs ← ConLeche.Cached.ruleRhsAtM lfe (absName c) (absName cj)
            (absName c) (absName cj) (absLevels us)
          let red ← ConLeche.Cached.mkAppNM rhs
            ((absExprs args).take r_p.val
              ++ (absExprs margs).drop (absRecRule rl).ctorParams)
          pure (some red)
        else pure none) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  -- sorry: on a 32-bit target `cnP as usize` (`core_c.rs:2056`) and
  -- `rP as usize` (`core_c.rs:2058`) truncate; see the module note on the
  -- `u64 → usize` casts.
  rcases System.Platform.numBits_eq with h32 | h64
  · sorry
  simp only [ConLeche.Cached.certAtI]
  unfold cached.core_c.iota_rec_telescopes_i at hok
  obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
  have hbv := Env.certs_refines hb
  rw [← hbv]
  cases b with
  | true =>
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨st1, fam⟩ := p
    obtain ⟨p1, hp1, hp⟩ := bind_eq_ok_iff.mp hp
    obtain ⟨fam1, st2⟩ := p1
    have hpe : (ok (st2, fam1) :
        Result (cached.state_c.CState ×
          (core.result.Result Bool core_types.CheckError))) = ok (st1, fam) := hp
    simp only [Result.ok.injEq, Prod.mk.injEq] at hpe
    obtain ⟨hs1, hf1⟩ := hpe
    rw [← hs1, ← hf1] at hok
    cases fam1 with
    | Err err => simp at hok
    | Ok fb =>
    obtain ⟨lst1, hrunF, hrel1, hwf1, -⟩ :=
      (iota_rec_family_i_refines hd d m_i r_p hc hcj hus husj hargs hmargs
        hmajor).apply hwf hfe hp1 hrel hfrel
    cases fb with
    | true =>
      obtain ⟨lst', hrunT, hrel', hwf', hrw⟩ :=
        telescopes_tail hfe hfrel r_p hc hcj hus hargs hmargs h64 hrel1 hwf1 hok
      refine ⟨lst', ?_, hrel', hwf', hrw⟩
      simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, if_true, ↓reduceIte] at hrunF hrunT ⊢
      simp only [hrunF, id_eq, ↓reduceIte]
      exact hrunT
    | false =>
      have hok' : (ok (core.result.Result.Ok none, st2) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      refine ⟨lst1, ?_, hrel1, hwf1, by simp⟩
      simp only [id_eq] at hrunF
      simp only [↓reduceIte]
      rw [run_bind hrunF]
      simp
  | false =>
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨st1, fam⟩ := p
    have hpe : (ok (st, core.result.Result.Ok true) :
        Result (cached.state_c.CState ×
          (core.result.Result Bool core_types.CheckError))) = ok (st1, fam) := hp
    simp only [Result.ok.injEq, Prod.mk.injEq] at hpe
    obtain ⟨hs1, hf1⟩ := hpe
    rw [← hs1, ← hf1] at hok
    obtain ⟨lst', hrunT, hrel', hwf', hrw⟩ :=
      telescopes_tail hfe hfrel r_p hc hcj hus hargs hmargs h64 hrel hwf hok
    refine ⟨lst', ?_, hrel', hwf', hrw⟩
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at hrunT ⊢
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hrunT

/-! ## `prepare_major_i` — the major premise's preparation (`core_c.rs:1693`) -/

/-- `ConLeche/Cached/CoreC.lean:698-708` — **`prepare_major_i` refines
`prepareMajorI`**: at a K-flagged recursor the K rescue runs on the *raw*
major and only then is the major head-normalized and its literal converted;
elsewhere the major is head-normalized first, its literal converted, and the
structure-eta rescue tried on the reduct (`core_c.rs:1693`).  The cited
`recName` argument is unused in `majorToCtorI` and dropped by the port, so it
is quantified. -/
theorem prepare_major_i_refines (hw : Wrappers mode fuel) (hd : IotaDeps mode fuel)
    (d : Std.U64) (rn : ConLeche.Name) {rules : alloc.vec.Vec env.RecRule}
    {major : expr.Expr} (hrules : RecRulesWF rules) (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.prepare_major_i mode fuel st fe d rules major)
      (fun lfe => ConLeche.Cached.prepareMajorI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val rn (absRecRules rules)
        (absExpr major)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.prepare_major_i at hok
  simp only [ConLeche.Cached.prepareMajorI]
  obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
  rw [← CoreK.rec_rule_k_refines hb]
  cases b with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r0, st1⟩ := p
    cases r0 with
    | Err err => simp at hok
    | Ok major_k =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hmkw⟩ :=
      (hd.majorToCtor d rn rules major hrules hmajor).apply hwf hfe hp hrel hfrel
    obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r1, st2⟩ := p1
    cases r1 with
    | Err err => simp at hok
    | Ok major0 =>
    obtain ⟨lst2, hrun2, hrel2, hwf2, hm0w⟩ :=
      (hw.whnfSim d hmkw).apply hwf1 hfe hp1 hrel1 hfrel
    obtain ⟨lst3, hrun3, hrel3, hwf3, hrw⟩ :=
      (hd.litMajorToCtor d major0 hm0w).apply hwf2 hfe hok hrel2 hfrel
    refine ⟨lst3, ?_, hrel3, hwf3, hrw⟩
    rw [run_bind hrun1, run_bind hrun2]
    exact hrun3
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r0, st1⟩ := p
    cases r0 with
    | Err err => simp at hok
    | Ok major0 =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hm0w⟩ :=
      (hw.whnfSim d hmajor).apply hwf hfe hp hrel hfrel
    obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r1, st2⟩ := p1
    cases r1 with
    | Err err => simp at hok
    | Ok major1 =>
    obtain ⟨lst2, hrun2, hrel2, hwf2, hm1w⟩ :=
      (hd.litMajorToCtor d major0 hm0w).apply hwf1 hfe hp1 hrel1 hfrel
    obtain ⟨lst3, hrun3, hrel3, hwf3, hrw⟩ :=
      (hd.majorToCtor d rn rules major1 hrules hm1w).apply hwf2 hfe hok hrel2 hfrel
    refine ⟨lst3, ?_, hrel3, hwf3, hrw⟩
    rw [run_bind hrun1, run_bind hrun2]
    exact hrun3

/-! ## `iota_rec_checks_i` — the firing cascade (`core_c.rs:1956`)

`iotaRecI`'s two comparand `let`s, the level comparison and the parameter
comparison (`certUnlessI mode keep`), and the telescopes block they gate. -/

/-- `core_k::lift_fueled` answers `.Ok b` only on `some b`. -/
private theorem lift_fueled_some {o : Option Bool} {b : Bool}
    (h : kernel.core_k.lift_fueled o = ok (core.result.Result.Ok b)) :
    o = some b := by
  cases o with
  | none =>
    simp only [kernel.core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce, -, hr⟩ := h
    simp at hr
  | some a =>
    simp only [kernel.core_k.lift_fueled, Result.ok.injEq,
      core.result.Result.Ok.injEq] at h
    rw [h]

/-- `pure`'s `run`. -/
private theorem run_pure {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_rec_checks_i` is `iotaRecI`'s
firing cascade**: the constructor's levels against the rule's comparands, then
the parameter comparison under `certUnlessI mode keep`, then the telescopes
block (`core_c.rs:1956`). -/
theorem iota_rec_checks_i_refines (hd : IotaDeps mode fuel) (d : Std.U64)
    {c cj : name.Name} {cv cvj : env.ConstantVal} (m_i r_p : Std.U64)
    {rl : env.RecRule} {us usj : alloc.vec.Vec level.Level}
    {args margs : alloc.vec.Vec expr.Expr} {major : expr.Expr}
    (hc : NameWF c) (hcj : NameWF cj) (hcv : ConstantValWF cv)
    (hcvj : ConstantValWF cvj) (hrl : RecRuleWF rl) (hus : LevelsWF us)
    (husj : LevelsWF usj) (hargs : ExprsWF args) (hmargs : ExprsWF margs)
    (hmajor : ExprWF major) :
    Sim (Option.map absExpr) (fun o => ∀ t, o = some t → ExprWF t)
      (fun st fe => cached.core_c.iota_rec_checks_i mode fuel st fe d c cj cv cvj
        m_i r_p rl us usj args margs major)
      (fun lfe => do
        let cmpLvls : List ConLeche.Level ←
          match (absRecRule rl).fire with
          | .nested lvls _ =>
              ConLeche.Cached.substLevelTreesM (absNames cv.level_params)
                (absLevels us) lvls
          | _ =>
              ConLeche.Cached.substLevelTreesM (absNames cv.level_params)
                (absLevels us)
                ((absNames cvj.level_params).map ConLeche.Level.param)
        let cmpArgs : List ConLeche.Cached.ExprC ←
          match (absRecRule rl).fire with
          | .nested _ pins =>
              ConLeche.Cached.pinArgsI (absNames cv.level_params) (absLevels us)
                ((absExprs args).take r_p.val) (r_p.val - 1) pins
          | _ => pure ((absExprs args).take (absRecRule rl).ctorParams)
        if ← ConLeche.liftFueled "level comparison"
            (← ConLeche.Cached.isEquivListLM (absLevels usj) cmpLvls) then do
          if ← (if (absRecRule rl).compareParams then
              ConLeche.Cached.certUnlessI (absMode mode)
                ((match (absRecRule rl).fire with
                  | .nested _ _ => true
                  | _ => false) || ConLeche.Name.isProjFnShape (absName c))
                (ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
                  ((absExprs margs).take (absRecRule rl).ctorParams) cmpArgs)
            else pure true) then
            if ← ConLeche.Cached.certAtI (absMode mode) (do
                let tyRec ← ConLeche.Cached.constTyAtM lfe (absName c) (absName c)
                  (absLevels us)
                if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                    (absMode mode).betaGate tyRec
                    ((absExprs args).take m_i.val ++ [absExpr major]) then do
                  let tyCtor ← ConLeche.Cached.constTyAtM lfe (absName cj) (absName cj)
                    (absLevels usj)
                  if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                      (absMode mode).betaGate tyCtor (absExprs margs) then
                    ConLeche.Cached.iotaIndexOkI (knot mode lfe fuel.val) lfe d.val
                      m_i.val r_p.val (absRecRule rl).ctorParams tyCtor
                      (absExprs margs) (((absExprs args).take m_i.val).drop r_p.val)
                  else pure false
                else pure false) then do
              let rhs ← ConLeche.Cached.ruleRhsAtM lfe (absName c) (absName cj)
                (absName c) (absName cj) (absLevels us)
              let red ← ConLeche.Cached.mkAppNM rhs
                ((absExprs args).take r_p.val
                  ++ (absExprs margs).drop (absRecRule rl).ctorParams)
              pure (some red)
            else pure none
          else pure none
        else pure none) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  -- sorry: on a 32-bit target `cnP as usize` (`core_c.rs:1994`) truncates, so
  -- the port's `take_exprs` peels a different prefix from con-leche's
  -- `margs.take rl.ctorParams`; see the module note on the `u64 → usize` casts.
  rcases System.Platform.numBits_eq with h32 | h64
  · sorry
  obtain ⟨-, hcvlps, -⟩ := hcv
  obtain ⟨-, hcvjlps, -⟩ := hcvj
  unfold cached.core_c.iota_rec_checks_i at hok
  obtain ⟨cmp_lvls, hcl, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hclv, hclw⟩ :=
    iota_cmp_levels_i_refines hrl hcvlps hus hcvjlps cmp_lvls hcl
  obtain ⟨cmp_args, hca, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hcav, hcaw⟩ := iota_cmp_args_i_refines hrl hcvlps hus hargs cmp_args hca
  cases hfire : rl.fire with
  | Nested lvls pins =>
    have hfa : (absRecRule rl).fire = ConLeche.RecRuleFire.nested (absLevels lvls) (absExprs pins) := by
      simp only [absRecRule, absFire, hfire]
    simp only [hfa] at hclv hcav ⊢
    rw [← hclv, ← hcav]
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨eqv, st1⟩ := p
    obtain ⟨lst1, hrunE, hrel1, hwf1⟩ :=
      StateC.is_equiv_list_l_m_refines hwf husj hclw hp lst hrel
    obtain ⟨rr, hlf, hok⟩ := bind_eq_ok_iff.mp hok
    cases rr with
    | Err err => simp at hok
    | Ok b =>
    rw [lift_fueled_some hlf] at hrunE
    rw [run_bind (run_pure _ lst), run_bind (run_pure _ lst), run_bind hrunE]
    simp only [ConLeche.liftFueled]
    rw [run_bind (run_pure b lst1)]
    cases b with
    | false =>
      have hok' : (ok (core.result.Result.Ok none, st1) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      exact ⟨lst1, by simp, hrel1, hwf1, by simp⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1v := Env.rec_rule_compare_params_refines hb1
      rw [← hb1v]
      obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨st2, rl1, pcmp⟩ := p1
      cases pcmp with
      | Err err => simp at hok
      | Ok pb =>
      obtain ⟨lstP, hrunP, hrelP, hwfP, hrl1⟩ :
          ∃ lstP, (if b1 then
                ConLeche.Cached.certUnlessI (absMode mode)
                  (true || ConLeche.Name.isProjFnShape (absName c))
                  (ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
                    ((absExprs margs).take (absRecRule rl).ctorParams)
                    (absExprs cmp_args))
              else pure true).run lst1 = .ok (pb, lstP)
            ∧ StateRel st2 lstP ∧ StateWF st2 ∧ rl1 = rl := by
        cases b1 with
        | false =>
          have he : (ok (st1, rl, core.result.Result.Ok true) :
              Result (cached.state_c.CState × env.RecRule ×
                (core.result.Result Bool core_types.CheckError)))
              = ok (st2, rl1, core.result.Result.Ok pb) := hp1
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at he
          obtain ⟨hs, hr1, hb⟩ := he
          cases hs; cases hr1; cases hb
          exact ⟨lst1, by simp, hrel1, hwf1, rfl⟩
        | true =>
          obtain ⟨keep, hkeep, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hkeepv := (iota_params_keep_i_refines hrl hc keep hkeep).1
          simp only [hfa] at hkeepv
          obtain ⟨b2, hb2, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hb2v := Env.certs_refines hb2
          simp only [ConLeche.Cached.certUnlessI, ← hb2v, ↓reduceIte]
          cases b2 with
          | true =>
            simp only [Bool.true_or, ↓reduceIte]
            rw [lift_eq] at hp1
            obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hi0v : i0.val = rl.ctor_params.val := by
              rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
            obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hpv : absExprs params = (absExprs margs).take rl.ctor_params.val := by
              rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                List.map_take]
            have hpw : ExprsWF params := by
              intro x hx
              rw [ExprOps.take_exprs_val hparams] at hx
              exact hmargs x (List.mem_of_mem_take hx)
            obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
            obtain ⟨pc, st3⟩ := p2
            have he : (ok (st3, rl, pc) :
                Result (cached.state_c.CState × env.RecRule ×
                  (core.result.Result Bool core_types.CheckError)))
                = ok (st2, rl1, core.result.Result.Ok pb) := hp1
            simp only [Result.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨hs, hr1, hb⟩ := he
            cases hs; cases hr1; cases hb
            obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
              (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                hfrel
            rw [hpv] at hrun2
            exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
          | false =>
            simp only [Bool.false_or]
            cases keep with
            | true =>
              rw [lift_eq] at hp1
              obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hi0v : i0.val = rl.ctor_params.val := by
                rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
              obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hpv : absExprs params
                  = (absExprs margs).take rl.ctor_params.val := by
                rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                  List.map_take]
              have hpw : ExprsWF params := by
                intro x hx
                rw [ExprOps.take_exprs_val hparams] at hx
                exact hmargs x (List.mem_of_mem_take hx)
              obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
              obtain ⟨pc, st3⟩ := p2
              have he : (ok (st3, rl, pc) :
                  Result (cached.state_c.CState × env.RecRule ×
                    (core.result.Result Bool core_types.CheckError)))
                  = ok (st2, rl1, core.result.Result.Ok pb) := hp1
              simp only [Result.ok.injEq, Prod.mk.injEq] at he
              obtain ⟨hs, hr1, hb⟩ := he
              cases hs; cases hr1; cases hb
              obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
                (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                  hfrel
              rw [hpv] at hrun2
              exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
            | false =>
              simp at hkeepv
      rw [run_bind hrunP]
      cases hrl1
      cases pb with
      | true =>
        simp only [↓reduceIte]
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrw⟩ :=
          (iota_rec_telescopes_i_refines hd d m_i r_p hc hcj hus husj hargs hmargs
            hmajor).apply hwfP hfe hok hrelP hfrel
        exact ⟨lst3, hrun3, hrel3, hwf3, hrw⟩
      | false =>
        have hok' : (ok (core.result.Result.Ok none, st2) :
            Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
              cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
        simp only [Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at hok'
        obtain ⟨hr, hs⟩ := hok'
        cases hr; cases hs
        exact ⟨lstP, by simp, hrelP, hwfP, by simp⟩

  | Inert =>
    have hfa : (absRecRule rl).fire = ConLeche.RecRuleFire.inert := by
      simp only [absRecRule, absFire, hfire]
    simp only [hfa] at hclv hcav ⊢
    rw [← hclv, ← hcav]
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨eqv, st1⟩ := p
    obtain ⟨lst1, hrunE, hrel1, hwf1⟩ :=
      StateC.is_equiv_list_l_m_refines hwf husj hclw hp lst hrel
    obtain ⟨rr, hlf, hok⟩ := bind_eq_ok_iff.mp hok
    cases rr with
    | Err err => simp at hok
    | Ok b =>
    rw [lift_fueled_some hlf] at hrunE
    rw [run_bind (run_pure _ lst), run_bind (run_pure _ lst), run_bind hrunE]
    simp only [ConLeche.liftFueled]
    rw [run_bind (run_pure b lst1)]
    cases b with
    | false =>
      have hok' : (ok (core.result.Result.Ok none, st1) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      exact ⟨lst1, by simp, hrel1, hwf1, by simp⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1v := Env.rec_rule_compare_params_refines hb1
      rw [← hb1v]
      obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨st2, rl1, pcmp⟩ := p1
      cases pcmp with
      | Err err => simp at hok
      | Ok pb =>
      obtain ⟨lstP, hrunP, hrelP, hwfP, hrl1⟩ :
          ∃ lstP, (if b1 then
                ConLeche.Cached.certUnlessI (absMode mode)
                  (false || ConLeche.Name.isProjFnShape (absName c))
                  (ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
                    ((absExprs margs).take (absRecRule rl).ctorParams)
                    (absExprs cmp_args))
              else pure true).run lst1 = .ok (pb, lstP)
            ∧ StateRel st2 lstP ∧ StateWF st2 ∧ rl1 = rl := by
        cases b1 with
        | false =>
          have he : (ok (st1, rl, core.result.Result.Ok true) :
              Result (cached.state_c.CState × env.RecRule ×
                (core.result.Result Bool core_types.CheckError)))
              = ok (st2, rl1, core.result.Result.Ok pb) := hp1
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at he
          obtain ⟨hs, hr1, hb⟩ := he
          cases hs; cases hr1; cases hb
          exact ⟨lst1, by simp, hrel1, hwf1, rfl⟩
        | true =>
          obtain ⟨keep, hkeep, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hkeepv := (iota_params_keep_i_refines hrl hc keep hkeep).1
          simp only [hfa] at hkeepv
          obtain ⟨b2, hb2, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hb2v := Env.certs_refines hb2
          simp only [ConLeche.Cached.certUnlessI, ← hb2v, ← hkeepv, ↓reduceIte]
          cases b2 with
          | true =>
            simp only [Bool.true_or, ↓reduceIte]
            rw [lift_eq] at hp1
            obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hi0v : i0.val = rl.ctor_params.val := by
              rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
            obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hpv : absExprs params = (absExprs margs).take rl.ctor_params.val := by
              rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                List.map_take]
            have hpw : ExprsWF params := by
              intro x hx
              rw [ExprOps.take_exprs_val hparams] at hx
              exact hmargs x (List.mem_of_mem_take hx)
            obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
            obtain ⟨pc, st3⟩ := p2
            have he : (ok (st3, rl, pc) :
                Result (cached.state_c.CState × env.RecRule ×
                  (core.result.Result Bool core_types.CheckError)))
                = ok (st2, rl1, core.result.Result.Ok pb) := hp1
            simp only [Result.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨hs, hr1, hb⟩ := he
            cases hs; cases hr1; cases hb
            obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
              (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                hfrel
            rw [hpv] at hrun2
            exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
          | false =>
            simp only [Bool.false_or]
            cases keep with
            | true =>
              rw [lift_eq] at hp1
              obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hi0v : i0.val = rl.ctor_params.val := by
                rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
              obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hpv : absExprs params
                  = (absExprs margs).take rl.ctor_params.val := by
                rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                  List.map_take]
              have hpw : ExprsWF params := by
                intro x hx
                rw [ExprOps.take_exprs_val hparams] at hx
                exact hmargs x (List.mem_of_mem_take hx)
              obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
              obtain ⟨pc, st3⟩ := p2
              have he : (ok (st3, rl, pc) :
                  Result (cached.state_c.CState × env.RecRule ×
                    (core.result.Result Bool core_types.CheckError)))
                  = ok (st2, rl1, core.result.Result.Ok pb) := hp1
              simp only [Result.ok.injEq, Prod.mk.injEq] at he
              obtain ⟨hs, hr1, hb⟩ := he
              cases hs; cases hr1; cases hb
              obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
                (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                  hfrel
              rw [hpv] at hrun2
              exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
            | false =>
              have he : (ok (st1, rl, core.result.Result.Ok true) :
                  Result (cached.state_c.CState × env.RecRule ×
                    (core.result.Result Bool core_types.CheckError)))
                  = ok (st2, rl1, core.result.Result.Ok pb) := hp1
              simp only [Result.ok.injEq, Prod.mk.injEq,
                core.result.Result.Ok.injEq] at he
              obtain ⟨hs, hr1, hb⟩ := he
              cases hs; cases hr1; cases hb
              exact ⟨lst1, by simp, hrel1, hwf1, rfl⟩
      rw [run_bind hrunP]
      cases hrl1
      cases pb with
      | true =>
        simp only [↓reduceIte]
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrw⟩ :=
          (iota_rec_telescopes_i_refines hd d m_i r_p hc hcj hus husj hargs hmargs
            hmajor).apply hwfP hfe hok hrelP hfrel
        exact ⟨lst3, hrun3, hrel3, hwf3, hrw⟩
      | false =>
        have hok' : (ok (core.result.Result.Ok none, st2) :
            Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
              cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
        simp only [Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at hok'
        obtain ⟨hr, hs⟩ := hok'
        cases hr; cases hs
        exact ⟨lstP, by simp, hrelP, hwfP, by simp⟩

  | Plain =>
    have hfa : (absRecRule rl).fire = ConLeche.RecRuleFire.plain := by
      simp only [absRecRule, absFire, hfire]
    simp only [hfa] at hclv hcav ⊢
    rw [← hclv, ← hcav]
    obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨eqv, st1⟩ := p
    obtain ⟨lst1, hrunE, hrel1, hwf1⟩ :=
      StateC.is_equiv_list_l_m_refines hwf husj hclw hp lst hrel
    obtain ⟨rr, hlf, hok⟩ := bind_eq_ok_iff.mp hok
    cases rr with
    | Err err => simp at hok
    | Ok b =>
    rw [lift_fueled_some hlf] at hrunE
    rw [run_bind (run_pure _ lst), run_bind (run_pure _ lst), run_bind hrunE]
    simp only [ConLeche.liftFueled]
    rw [run_bind (run_pure b lst1)]
    cases b with
    | false =>
      have hok' : (ok (core.result.Result.Ok none, st1) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      exact ⟨lst1, by simp, hrel1, hwf1, by simp⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1v := Env.rec_rule_compare_params_refines hb1
      rw [← hb1v]
      obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨st2, rl1, pcmp⟩ := p1
      cases pcmp with
      | Err err => simp at hok
      | Ok pb =>
      obtain ⟨lstP, hrunP, hrelP, hwfP, hrl1⟩ :
          ∃ lstP, (if b1 then
                ConLeche.Cached.certUnlessI (absMode mode)
                  (false || ConLeche.Name.isProjFnShape (absName c))
                  (ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
                    ((absExprs margs).take (absRecRule rl).ctorParams)
                    (absExprs cmp_args))
              else pure true).run lst1 = .ok (pb, lstP)
            ∧ StateRel st2 lstP ∧ StateWF st2 ∧ rl1 = rl := by
        cases b1 with
        | false =>
          have he : (ok (st1, rl, core.result.Result.Ok true) :
              Result (cached.state_c.CState × env.RecRule ×
                (core.result.Result Bool core_types.CheckError)))
              = ok (st2, rl1, core.result.Result.Ok pb) := hp1
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at he
          obtain ⟨hs, hr1, hb⟩ := he
          cases hs; cases hr1; cases hb
          exact ⟨lst1, by simp, hrel1, hwf1, rfl⟩
        | true =>
          obtain ⟨keep, hkeep, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hkeepv := (iota_params_keep_i_refines hrl hc keep hkeep).1
          simp only [hfa] at hkeepv
          obtain ⟨b2, hb2, hp1⟩ := bind_eq_ok_iff.mp hp1
          have hb2v := Env.certs_refines hb2
          simp only [ConLeche.Cached.certUnlessI, ← hb2v, ← hkeepv, ↓reduceIte]
          cases b2 with
          | true =>
            simp only [Bool.true_or, ↓reduceIte]
            rw [lift_eq] at hp1
            obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hi0v : i0.val = rl.ctor_params.val := by
              rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
            obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
            have hpv : absExprs params = (absExprs margs).take rl.ctor_params.val := by
              rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                List.map_take]
            have hpw : ExprsWF params := by
              intro x hx
              rw [ExprOps.take_exprs_val hparams] at hx
              exact hmargs x (List.mem_of_mem_take hx)
            obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
            obtain ⟨pc, st3⟩ := p2
            have he : (ok (st3, rl, pc) :
                Result (cached.state_c.CState × env.RecRule ×
                  (core.result.Result Bool core_types.CheckError)))
                = ok (st2, rl1, core.result.Result.Ok pb) := hp1
            simp only [Result.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨hs, hr1, hb⟩ := he
            cases hs; cases hr1; cases hb
            obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
              (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                hfrel
            rw [hpv] at hrun2
            exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
          | false =>
            simp only [Bool.false_or]
            cases keep with
            | true =>
              rw [lift_eq] at hp1
              obtain ⟨i0, hi0, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hi0v : i0.val = rl.ctor_params.val := by
                rw [← Result.ok_injective hi0]; exact cast_usize_val_64 h64 _
              obtain ⟨params, hparams, hp1⟩ := bind_eq_ok_iff.mp hp1
              have hpv : absExprs params
                  = (absExprs margs).take rl.ctor_params.val := by
                rw [absExprs, ExprOps.take_exprs_val hparams, hi0v, absExprs,
                  List.map_take]
              have hpw : ExprsWF params := by
                intro x hx
                rw [ExprOps.take_exprs_val hparams] at hx
                exact hmargs x (List.mem_of_mem_take hx)
              obtain ⟨p2, hp2, hp1⟩ := bind_eq_ok_iff.mp hp1
              obtain ⟨pc, st3⟩ := p2
              have he : (ok (st3, rl, pc) :
                  Result (cached.state_c.CState × env.RecRule ×
                    (core.result.Result Bool core_types.CheckError)))
                  = ok (st2, rl1, core.result.Result.Ok pb) := hp1
              simp only [Result.ok.injEq, Prod.mk.injEq] at he
              obtain ⟨hs, hr1, hb⟩ := he
              cases hs; cases hr1; cases hb
              obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
                (hd.defEqList d params cmp_args hpw hcaw).apply hwf1 hfe hp2 hrel1
                  hfrel
              rw [hpv] at hrun2
              exact ⟨lst2, hrun2, hrel2, hwf2, rfl⟩
            | false =>
              have he : (ok (st1, rl, core.result.Result.Ok true) :
                  Result (cached.state_c.CState × env.RecRule ×
                    (core.result.Result Bool core_types.CheckError)))
                  = ok (st2, rl1, core.result.Result.Ok pb) := hp1
              simp only [Result.ok.injEq, Prod.mk.injEq,
                core.result.Result.Ok.injEq] at he
              obtain ⟨hs, hr1, hb⟩ := he
              cases hs; cases hr1; cases hb
              exact ⟨lst1, by simp, hrel1, hwf1, rfl⟩
      rw [run_bind hrunP]
      cases hrl1
      cases pb with
      | true =>
        simp only [↓reduceIte]
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrw⟩ :=
          (iota_rec_telescopes_i_refines hd d m_i r_p hc hcj hus husj hargs hmargs
            hmajor).apply hwfP hfe hok hrelP hfrel
        exact ⟨lst3, hrun3, hrel3, hwf3, hrw⟩
      | false =>
        have hok' : (ok (core.result.Result.Ok none, st2) :
            Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
              cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
        simp only [Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at hok'
        obtain ⟨hr, hs⟩ := hok'
        cases hr; cases hs
        exact ⟨lstP, by simp, hrelP, hwfP, by simp⟩


/-! ## `iota_rec_rule_i` — the prepared major's rule (`core_c.rs:1852`)

`iotaRecI`'s `match ExprC.getAppFn major with | .const cj usj => …`: the head
must be a stored constructor with a matching rule at a matching spine length,
and a matched **inert** rule declines with `notImplemented`. -/

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_rec_rule_i` is `iotaRecI`'s
constructor-head/rule dispatch** (`core_c.rs:1852`). -/
theorem iota_rec_rule_i_refines (hd : IotaDeps mode fuel) (d : Std.U64)
    {c : name.Name} {cv : env.ConstantVal} (m_i r_p : Std.U64)
    {rules : alloc.vec.Vec env.RecRule} {us : alloc.vec.Vec level.Level}
    {args : alloc.vec.Vec expr.Expr} {major : expr.Expr}
    (hc : NameWF c) (hcv : ConstantValWF cv) (hrules : RecRulesWF rules)
    (hus : LevelsWF us) (hargs : ExprsWF args) (hmajor : ExprWF major) :
    Sim (Option.map absExpr) (fun o => ∀ t, o = some t → ExprWF t)
      (fun st fe => cached.core_c.iota_rec_rule_i mode fuel st fe d c cv m_i r_p
        rules us args major)
      (fun lfe =>
        match ConLeche.Cached.ExprC.getAppFn (absExpr major) with
        | .const cj usj => do
          let cjn ← pure cj
          match lfe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match (absRecRules rules).find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← pure (ConLeche.Cached.ExprC.getAppArgs (absExpr major))
              if margs.length = rl.ctorParams + rl.nfields then
                if rl.fire = .inert then
                  throw (.notImplemented
                    "iota reduction over a nested auxiliary recursor rule")
                else do
                  let cmpLvls : List ConLeche.Level ←
                    match rl.fire with
                    | .nested lvls _ =>
                        ConLeche.Cached.substLevelTreesM (absNames cv.level_params)
                          (absLevels us) lvls
                    | _ =>
                        ConLeche.Cached.substLevelTreesM (absNames cv.level_params)
                          (absLevels us)
                          ((cvj.levelParams).map ConLeche.Level.param)
                  let cmpArgs : List ConLeche.Cached.ExprC ←
                    match rl.fire with
                    | .nested _ pins =>
                        ConLeche.Cached.pinArgsI (absNames cv.level_params)
                          (absLevels us) ((absExprs args).take r_p.val)
                          (r_p.val - 1) pins
                    | _ => pure ((absExprs args).take rl.ctorParams)
                  if ← ConLeche.liftFueled "level comparison"
                      (← ConLeche.Cached.isEquivListLM (usj) cmpLvls) then do
                    if ← (if rl.compareParams then
                        ConLeche.Cached.certUnlessI (absMode mode)
                          ((match rl.fire with
                            | .nested _ _ => true
                            | _ => false) || ConLeche.Name.isProjFnShape (absName c))
                          (ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
                            ((margs).take rl.ctorParams) cmpArgs)
                      else pure true) then
                      if ← ConLeche.Cached.certAtI (absMode mode) (do
                          let tyRec ← ConLeche.Cached.constTyAtM lfe (absName c) (absName c)
                            (absLevels us)
                          if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                              (absMode mode).betaGate tyRec
                              ((absExprs args).take m_i.val ++ [absExpr major]) then do
                            let tyCtor ← ConLeche.Cached.constTyAtM lfe (cj) (cj)
                              (usj)
                            if ← ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
                                (absMode mode).betaGate tyCtor (margs) then
                              ConLeche.Cached.iotaIndexOkI (knot mode lfe fuel.val) lfe d.val
                                m_i.val r_p.val rl.ctorParams tyCtor
                                (margs) (((absExprs args).take m_i.val).drop r_p.val)
                            else pure false
                          else pure false) then do
                        let rhs ← ConLeche.Cached.ruleRhsAtM lfe (absName c) (cj)
                          (absName c) (cj) (absLevels us)
                        let red ← ConLeche.Cached.mkAppNM rhs
                          ((absExprs args).take r_p.val
                            ++ (margs).drop rl.ctorParams)
                        pure (some red)
                      else pure none
                    else pure none
                  else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.iota_rec_rule_i at hok
  obtain ⟨fj, hfj, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hfjv, hfjw⟩ := ExprOps.get_app_fn_refines hmajor hfj
  rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hfjv]
  obtain ⟨⟨dd, kk⟩⟩ := fj
  cases kk with
  | Const cj usj =>
    obtain ⟨hcjw, husjw⟩ := CoreK.wf_const_inv hfjw rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at hok
    simp only [absExpr_mk, absExprKind, pure_bind]
    obtain ⟨o, ho, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hov, how⟩ :=
      CoreK.ctor_probe_refines (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe)
        hcjw ho
    cases hfind : lfe.find? (absName cj) with
    | none =>
      rw [hfind] at hov
      simp only [hfind]
      simp only [CoreK.ctorOf, Option.map_eq_none_iff] at hov
      subst hov
      have hok' : (ok (core.result.Result.Ok none, st) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      exact ⟨lst, by simp, hrel, hwf, by simp⟩
    | some ci =>
      rw [hfind] at hov
      cases ci with
      | ctorInfo cvj nP nF =>
        simp only [hfind]
        simp only [CoreK.ctorOf, Option.map_eq_some_iff] at hov
        obtain ⟨t, rfl, ht⟩ := hov
        obtain ⟨cvj0, nP0, nF0⟩ := t
        simp only [Prod.mk.injEq] at ht
        obtain ⟨hcvj0, -, -⟩ := ht
        have hcvj0w : ConstantValWF cvj0 := how cvj0 nP0 nF0 rfl
        obtain ⟨o1, ho1, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨-, hfindr⟩ := CoreK.rules_find_refines hrules hcjw ho1
        cases o1 with
        | none =>
          have hfindr' : (none : Option ConLeche.RecRule)
              = (absRecRules rules).find? (fun r' => r'.ctor == absName cj) := hfindr
          rw [← hfindr']
          have hok' : (ok (core.result.Result.Ok none, st) :
              Result ((core.result.Result (Option expr.Expr)
                core_types.CheckError) × cached.state_c.CState))
              = ok (core.result.Result.Ok r, st') := hok
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at hok'
          obtain ⟨hr, hs⟩ := hok'
          cases hr; cases hs
          exact ⟨lst, by simp, hrel, hwf, by simp⟩
        | some k =>
          have hfindr' : (absRecRules rules)[k.val]?
              = (absRecRules rules).find? (fun r' => r'.ctor == absName cj) := hfindr
          obtain ⟨rr, hrr, hok⟩ := bind_eq_ok_iff.mp hok
          have hrrg := ExprOps.vec_index_getElem? hrr
          obtain ⟨rl, hrl, hok⟩ := bind_eq_ok_iff.mp hok
          have hrlv : rl = rr := Env.rec_rule_dup_refines hrl
          have hrrl : (absRecRules rules)[k.val]? = some (absRecRule rl) := by
            rw [absRecRules, List.getElem?_map, hrrg, hrlv]; rfl
          rw [hrrl] at hfindr'
          simp only [← hfindr']
          have hrlw : RecRuleWF rl := by
            have hmem : rr ∈ rules.val := by
              have hg := hrrg
              rw [List.getElem?_eq_some_iff] at hg
              obtain ⟨hlt, he⟩ := hg
              rw [← he]; exact List.getElem_mem hlt
            rw [hrlv]; exact hrules rr hmem
          obtain ⟨margs, hmargs0, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨hmav, hmaw⟩ := ExprOps.get_app_args_refines hmajor hmargs0
          rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← hmav]
          rw [lift_eq] at hok
          obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
          have hi1v : i1.val = margs.val.length := by
            rw [← Result.ok_injective hi1, Env.usize_cast_u64_val,
              alloc.vec.Vec.len_val]
          obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
          have hi2v : i2.val = rl.ctor_params.val + rl.nfields.val :=
            HashMap.uscalar_add_eq hi2
          split at hok
          · rename_i hne
            simp only [bne_iff_ne, ne_eq] at hne
            rw [if_neg (show ¬ ((absExprs margs).length
                = (absRecRule rl).ctorParams + (absRecRule rl).nfields) by
              simp only [absExprs, List.length_map, absRecRule]
              intro hcon
              exact hne (by scalar_tac))]
            have hok' : (ok (core.result.Result.Ok none, st) :
                Result ((core.result.Result (Option expr.Expr)
                  core_types.CheckError) × cached.state_c.CState))
                = ok (core.result.Result.Ok r, st') := hok
            simp only [Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at hok'
            obtain ⟨hr, hs⟩ := hok'
            cases hr; cases hs
            exact ⟨lst, by simp, hrel, hwf, by simp⟩
          · rename_i hne
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
            rw [if_pos (show (absExprs margs).length
                = (absRecRule rl).ctorParams + (absRecRule rl).nfields by
              simp only [absExprs, List.length_map, absRecRule]
              rw [hne] at hi1v
              scalar_tac)]
            obtain ⟨bi, hbi, hok⟩ := bind_eq_ok_iff.mp hok
            have hbiv := CoreK.fire_is_inert_refines hbi
            cases bi with
            | true =>
              exfalso
              obtain ⟨s1, -, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨v1, -, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨ce, -, hok⟩ := bind_eq_ok_iff.mp hok
              simp at hok
            | false =>
              rw [if_neg (show ¬ ((absRecRule rl).fire = ConLeche.RecRuleFire.inert) by
                intro hcon
                simp only [absRecRule] at hcon
                rw [hcon] at hbiv
                simp at hbiv)]
              have hok2 : cached.core_c.iota_rec_checks_i mode fuel st fe d c cj
                  cv cvj0 m_i r_p rl us usj args margs major
                  = ok (core.result.Result.Ok r, st') := hok
              rw [← hcvj0]
              exact (iota_rec_checks_i_refines hd d m_i r_p hc hcjw hcv hcvj0w
                hrlw hus husjw hargs hmaw hmajor).apply hwf hfe hok2 hrel hfrel
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _
      | recInfo _ _ _ _ | projInfo _ =>
        simp only [hfind]
        simp only [CoreK.ctorOf, Option.map_eq_none_iff] at hov
        subst hov
        have hok' : (ok (core.result.Result.Ok none, st) :
            Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
              cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
        simp only [Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at hok'
        obtain ⟨hr, hs⟩ := hok'
        cases hr; cases hs
        exact ⟨lst, by simp, hrel, hwf, by simp⟩
  | Bvar _ | Fvar _ _ | «Sort» _ | App _ _ | Lam _ _ _ | ForallE _ _ _
  | LetE _ _ _ | Lit _ | Proj _ _ _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at hok
    simp only [absExpr_mk, absExprKind]
    have hok' : (ok (core.result.Result.Ok none, st) :
        Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
          cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
    obtain ⟨hr, hs⟩ := hok'
    cases hr; cases hs
    exact ⟨lst, by simp, hrel, hwf, by simp⟩

/-! ## `iota_rec_i` — the ι step (`core_c.rs:1814`)

The head/arity dispatch, and the whole ι cone behind it: this is the theorem
`Arms/App.lean`'s spine loop consumes, together with `iota_arity_ok_refines`. -/

/-- `ConLeche/Cached/CoreC.lean:743-838` — **`iota_rec_i` refines `iotaRecI`**:
one ι step (`core_c.rs:1814`).  The `Option` result carries `ExprWF` in the
`∀ x ∈ o` form `Arms/App.lean` consumes. -/
theorem iota_rec_i_refines (hw : Wrappers mode fuel) (hd : IotaDeps mode fuel)
    (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim (Option.map absExpr) (fun o => ∀ x ∈ o, ExprWF x)
      (fun st fe => cached.core_c.iota_rec_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.iotaRecI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (absExpr e)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  simp only [ConLeche.Cached.iotaRecI]
  unfold cached.core_c.iota_rec_i at hok
  obtain ⟨f, hf, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hfv, hfw⟩ := ExprOps.get_app_fn_refines he hf
  rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hfv]
  obtain ⟨⟨dd, kk⟩⟩ := f
  cases kk with
  | Const c us =>
    obtain ⟨hcw, husw⟩ := CoreK.wf_const_inv hfw rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at hok
    simp only [absExpr_mk, absExprKind, pure_bind]
    obtain ⟨o, ho, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hov, how⟩ :=
      CoreK.rec_probe_refines (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe)
        hcw ho
    cases hfind : lfe.find? (absName c) with
    | none =>
      rw [hfind] at hov
      simp only [hfind]
      simp only [CoreK.recOf, Option.map_eq_none_iff] at hov
      subst hov
      have hok' : (ok (core.result.Result.Ok none, st) :
          Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
            cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hok'
      obtain ⟨hr, hs⟩ := hok'
      cases hr; cases hs
      exact ⟨lst, by simp, hrel, hwf, by simp⟩
    | some ci =>
      rw [hfind] at hov
      cases ci with
      | recInfo cvL mIL rPL rulesL =>
        simp only [hfind]
        simp only [CoreK.recOf, Option.map_eq_some_iff] at hov
        obtain ⟨t, hot, ht⟩ := hov
        obtain ⟨cv, m_i, r_p, rules⟩ := t
        simp only [Prod.mk.injEq] at ht
        obtain ⟨hcvL, hmiL, hrpL, hrulesL⟩ := ht
        obtain ⟨hcvw, hruleswf⟩ := how cv m_i r_p rules hot
        rw [hot] at hok
        rw [← hcvL, ← hmiL, ← hrpL, ← hrulesL]
        obtain ⟨args, hargs0, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hargsv, hargsw⟩ := ExprOps.get_app_args_refines he hargs0
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← hargsv]
        rw [lift_eq] at hok
        obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
        have hi1v : i1.val = args.val.length := by
          rw [← Result.ok_injective hi1, Env.usize_cast_u64_val,
            alloc.vec.Vec.len_val]
        obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
        have hi2v : i2.val = m_i.val + 1 := HashMap.uscalar_add_eq hi2
        split at hok
        · rename_i heq
          split at hok
          · rename_i heq2
            rw [if_pos (show (absExprs args).length = m_i.val + 1
                ∧ (absLevels us).length
                  = (absConstantVal cv).levelParams.length by
              constructor
              · simp only [absExprs, List.length_map]
                rw [heq] at hi1v
                scalar_tac
              · simp only [absLevels, absConstantVal, absNames, List.length_map]
                have h3 : (alloc.vec.Vec.len us).val = us.val.length :=
                  alloc.vec.Vec.len_val us
                have h4 : (alloc.vec.Vec.len cv.level_params).val
                    = cv.level_params.val.length :=
                  alloc.vec.Vec.len_val cv.level_params
                rw [heq2] at h3
                omega)]
            obtain ⟨raw, hraw, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨hrawv, hraww⟩ := CoreK.get_d_expr_refines hargsw hraw
            obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨rr0, st1⟩ := p
            cases rr0 with
            | Err err => simp at hok
            | Ok major =>
            obtain ⟨lst1, hrun1, hrel1, hwf1, hmajw⟩ :=
              (prepare_major_i_refines hw hd d (absName c) hruleswf hraww).apply
                hwf hfe hp hrel hfrel
            rw [hrawv] at hrun1
            simp only [ConLeche.Expr.mkBvar_eq]
            rw [run_bind hrun1]
            exact (iota_rec_rule_i_refines hd d m_i r_p hcw hcvw hruleswf husw
              hargsw hmajw).apply hwf1 hfe hok hrel1 hfrel
          · rename_i heq2
            rw [if_neg (show ¬ ((absExprs args).length = m_i.val + 1
                ∧ (absLevels us).length
                  = (absConstantVal cv).levelParams.length) by
              rintro ⟨-, h2⟩
              apply heq2
              simp only [absLevels, absConstantVal, absNames, List.length_map] at h2
              have h3 := alloc.vec.Vec.len_val us
              have h4 := alloc.vec.Vec.len_val cv.level_params
              scalar_tac)]
            have hok' : (ok (core.result.Result.Ok none, st) :
                Result ((core.result.Result (Option expr.Expr)
                  core_types.CheckError) × cached.state_c.CState))
                = ok (core.result.Result.Ok r, st') := hok
            simp only [Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at hok'
            obtain ⟨hr, hs⟩ := hok'
            cases hr; cases hs
            exact ⟨lst, by simp, hrel, hwf, by simp⟩
        · rename_i heq
          rw [if_neg (show ¬ ((absExprs args).length = m_i.val + 1
              ∧ (absLevels us).length
                = (absConstantVal cv).levelParams.length) by
            rintro ⟨h1, -⟩
            apply heq
            simp only [absExprs, List.length_map] at h1
            scalar_tac)]
          have hok' : (ok (core.result.Result.Ok none, st) :
              Result ((core.result.Result (Option expr.Expr)
                core_types.CheckError) × cached.state_c.CState))
              = ok (core.result.Result.Ok r, st') := hok
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at hok'
          obtain ⟨hr, hs⟩ := hok'
          cases hr; cases hs
          exact ⟨lst, by simp, hrel, hwf, by simp⟩
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _
      | ctorInfo _ _ _ | projInfo _ =>
        simp only [hfind]
        simp only [CoreK.recOf, Option.map_eq_none_iff] at hov
        subst hov
        have hok' : (ok (core.result.Result.Ok none, st) :
            Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
              cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
        simp only [Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at hok'
        obtain ⟨hr, hs⟩ := hok'
        cases hr; cases hs
        exact ⟨lst, by simp, hrel, hwf, by simp⟩
  | Bvar _ | Fvar _ _ | «Sort» _ | App _ _ | Lam _ _ _ | ForallE _ _ _
  | LetE _ _ _ | Lit _ | Proj _ _ _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at hok
    simp only [absExpr_mk, absExprKind]
    have hok' : (ok (core.result.Result.Ok none, st) :
        Result ((core.result.Result (Option expr.Expr) core_types.CheckError) ×
          cached.state_c.CState)) = ok (core.result.Result.Ok r, st') := hok
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok'
    obtain ⟨hr, hs⟩ := hok'
    cases hr; cases hs
    exact ⟨lst, by simp, hrel, hwf, by simp⟩

/-! ## The two plain-equation corollaries `Arms/App.lean` consumes

`iota_arity_ok` and `is_ctor_stored_i` are pure `Bool`s; the spine loop wants
them as equations rather than as `SimP`, which is what these two are. -/

/-- `iota_arity_ok_refines`, as the equation `Arms/App.lean` uses. -/
theorem iota_arity_ok_eq (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (e : expr.Expr)
    (b : Bool) (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe) (he : ExprWF e)
    (h : cached.core_c.iota_arity_ok fe e = ok b) :
    b = ConLeche.Cached.iotaArityOk lfe (absExpr e) :=
  (iota_arity_ok_refines hfe hrel he b h).1

/-- `is_ctor_stored_i_refines`, as the equation `Arms/App.lean` uses. -/
theorem is_ctor_stored_i_eq (fe : fenv.FEnv) (lfe : ConLeche.FEnv)
    (c : name.Name) (b : Bool) (hfe : FEnvWF fe) (hrel : FEnvRel fe lfe)
    (hc : NameWF c) (h : cached.core_c.is_ctor_stored_i fe c = ok b) :
    b = (match lfe.find? (absName c) with
         | some (.ctorInfo _ _ _) => true
         | _ => false) :=
  (is_ctor_stored_i_refines hfe hrel hc b h).1

end

end ConRon.Refine.Core

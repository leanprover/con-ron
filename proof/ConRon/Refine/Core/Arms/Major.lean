/-
# The knot's arms: the major premise to constructor form (task #55)

`crates/con-ron-core/src/cached/core_c.rs`'s `major_to_ctor_*` group against
con-leche's `majorToCtorI` (`ConLeche/Cached/CoreC.lean:543-670`) and the two
literal conversions `litMajorToCtorI` (`:672-681`) and `projLitToCtorI`
(`:683-692`).

## The split

con-leche's `majorToCtorI` is one long function: a cheap syntactic dispatch
(`isCtorAppC`, a *single* recursor rule, the rule's constructor stored, its
type's `piResult` headed by a stored inductive) followed by **three** `if`
arms, one per install-time rescue bit — `rl.k`, `rl.eta` and the `And`-only
rescue.  The port splits it into four functions: `major_to_ctor_i` is the
dispatch, and `major_to_ctor_k_i` / `major_to_ctor_eta_i` /
`major_to_ctor_and_i` are the three arms; two tails shared between arms are
factored out further (`k_type_and_irrel_i`, `eta_rescue_certs_i`), and the
`r.whnf depth (← r.inferIO depth major)` all three arms open with is
`infer_io_whnf_i` (another agent's file).

So that the four statements *add up to* `majorToCtorI` and nothing is assumed,
the three clauses are **named here** (`majorToCtorKClause`,
`majorToCtorEtaClause`, `majorToCtorAndClause`, with their two shared tails
`kTypeAndIrrelTail` and `etaRescueCertsTail`) as literal transcriptions of the
cited lines, and `majorToCtorI_eq_k` / `_eq_eta` / `_eq_and` / `_eq_stuck`
*prove* — by `simp` against the cited definition — that `majorToCtorI` is that
clause under the dispatch's guards.  Each arm's theorem is then stated against
its clause, and `major_to_ctor_i_refines` glues them back onto `majorToCtorI`.

## The certificate read, at both modes

`majorToCtorI` runs `constTyAtM fe ctorI rl.ctor ust` **outside** `certAtI` in
all three arms (`ConLeche/Cached/CoreC.lean:574`, `:619`, `:653`), and since
task #61 so does the port (`core_c.rs:1385`, `:1515`, `:1621`): the read is
unconditional and only the `iotaCertsI` behind it sits under
`if env::certs(mode)`.  That matters because `constTyAtM` is a *memoising*
action (`ConLeche/Cached/StateC.lean:332-349`: on a miss it inserts into
`CState.constTyAt`), so at `.trusted` — where `certs = false` — con-leche
still moves the state, and the port now moves it too.  Each arm therefore
applies `const_ty_at_m_refines` *before* splitting on `env::certs`, and the
two modes differ only in whether `iotaCertsI` runs; nothing here is `sorry`.

## The full outcome (task #67)

Every lemma below is stated with `Refine/State.lean`'s `Out`: the exact result
on success, and — on a Rust `Err` at one of the three mirrored constructors —
con-leche's own throw at the *same kind*.  That half is cheap here because
**none of these functions throws on its own**: `core_c.rs`'s `major_to_ctor_*`
group has no `Err(core_types::invalid(…))` arm at all, every `match` failure
falling through to `major` unchanged, so each of the fifteen failure cases is
move 1 — the callee's `…apply_err` carried across con-leche's `do` block by
`ErrSim.bindCM` (`ErrSim.bindCM2` where one Rust call, `infer_io_whnf_i`,
stands for con-leche's *two* steps).  The clauses' own sub-actions —
`constTyAtM` (`StateC.const_ty_at_m_err`), `iotaCertsI`, `proofIrrelI`,
`structEtaCertWithI`, the four wrappers — are where an error can enter, and
each is the same call on both sides.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

open ConRon.Refine.CoreK

section Clauses
open ConLeche ConLeche.Cached

/-- `ConLeche/Cached/CoreC.lean:589-596` and `:655-662` — the K arm's last two
certificates, shared with the `And` arm: the port's `k_type_and_irrel_i`. -/
def kTypeAndIrrelTail (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (tmaj fab major : ExprC) : CheckCM ExprC := do
  let tfab ← r.inferIO depth fab
  if ← r.defeq depth tmaj tfab then
    if ← certAtI mode (proofIrrelI r fe depth fab major) then
      pure fab
    else pure major
  else pure major

/-- `ConLeche/Cached/CoreC.lean:628-635` — the η arm's certificate and its
0-field proof-irrelevance rescue: the port's `eta_rescue_certs_i`. -/
def etaRescueCertsTail (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (fab major tmaj : ExprC) (caps : IndCaps) : CheckCM ExprC := do
  if ← structEtaCertWithI mode r fe depth fab major tmaj then
    pure fab
  else if caps.etaFields = 0 then
    if ← proofIrrelI r fe depth fab major then pure fab else pure major
  else pure major

/-- `ConLeche/Cached/CoreC.lean:556-598` — **the `rl.k` clause** of
`majorToCtorI`: the port's `major_to_ctor_k_i`. -/
def majorToCtorKClause (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (rl : RecRule) (cvj : ConstantVal) (cnP : Nat) (T : Name) (major : ExprC) :
    CheckCM ExprC := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match ExprC.getAppFn tmaj with
  | .const T' ust =>
    if (← pure (T' == T)) ∧ cvj.levelParams.length = ust.length then do
      let margs ← pure (ExprC.getAppArgs tmaj)
      if cnP ≤ margs.length then do
        let ctorI ← pure rl.ctor
        let h ← pure (Expr.const ctorI ust)
        let fab ← mkAppNM h (margs.take cnP)
        if ← pure (ExprC.wscopedB depth fab && ExprC.looseBVarsBounded 0 fab &&
            ExprC.leafGuard fab major) then do
          let tyCtor ← constTyAtM fe ctorI rl.ctor ust
          if ← certAtI mode (iotaCertsI r fe depth false tyCtor (margs.take cnP)) then
            kTypeAndIrrelTail mode r fe depth tmaj fab major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- `ConLeche/Cached/CoreC.lean:599-637` — **the `rl.eta` clause** of
`majorToCtorI`: the port's `major_to_ctor_eta_i`. -/
def majorToCtorEtaClause (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (rl : RecRule) (cvT : ConstantVal) (caps : IndCaps) (T : Name) (major : ExprC) :
    CheckCM ExprC := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match ExprC.getAppFn tmaj with
  | .const T' ust => do
    let margs ← pure (ExprC.getAppArgs tmaj)
    let ustL ← pure ust
    if (← pure (T' == T)) ∧ margs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        capsNeverZero cvT.levelParams ustL caps = true then do
      let TI ← pure T
      let projs ← projAppsI fe T TI ust margs major caps.etaFields
      let ctorI ← pure caps.etaCtor
      let h ← pure (Expr.const ctorI ust)
      let fab ← mkAppNM h (margs ++ projs)
      if ← pure (ExprC.wscopedB depth fab && ExprC.looseBVarsBounded 0 fab &&
          ExprC.leafGuard fab major) then do
        let tyCtor ← constTyAtM fe ctorI rl.ctor ust
        if ← certAtI mode (iotaCertsI r fe depth false tyCtor (margs ++ projs)) then
          etaRescueCertsTail mode r fe depth fab major tmaj caps
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- `ConLeche/Cached/CoreC.lean:638-666` — **the `And` clause** of
`majorToCtorI`: the port's `major_to_ctor_and_i`. -/
def majorToCtorAndClause (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (rl : RecRule) (cvj : ConstantVal) (cnP : Nat) (T : Name) (major : ExprC) :
    CheckCM ExprC := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match ExprC.getAppFn tmaj with
  | .const T' ust => do
    let margs ← pure (ExprC.getAppArgs tmaj)
    if (← pure (T' == T)) ∧ margs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        fe.andRescueSlotsF rl.ctor cnP ust = true then do
      let TI ← pure T
      let projs ← projNodesI TI major [0, 1]
      let ctorI ← pure rl.ctor
      let h ← pure (Expr.const ctorI ust)
      let fab ← mkAppNM h (margs ++ projs)
      if ← pure (ExprC.wscopedB depth fab && ExprC.looseBVarsBounded 0 fab &&
          ExprC.leafGuard fab major) then do
        let tyCtor ← constTyAtM fe ctorI rl.ctor ust
        if ← certAtI mode (iotaCertsI r fe depth false tyCtor (margs ++ projs)) then
          kTypeAndIrrelTail mode r fe depth tmaj fab major
        else pure major
      else pure major
    else pure major
  | _ => pure major

end Clauses

/-! ## `majorToCtorI` *is* its four clauses

Each of these is the cited definition rewritten once and its dispatch
discharged: nothing is assumed about the clauses, they are `majorToCtorI`'s
own subterms. -/

section Decompose
open ConLeche ConLeche.Cached
variable (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat) (recName : Name)

/-- The `rl.k` clause. -/
theorem majorToCtorI_eq_k {rules : List RecRule} {rl : RecRule} {cvj cvT : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us : List Level} {caps : IndCaps} {major : ExprC}
    (hctor : isCtorAppC fe major = false) (hrules : rules = [rl])
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T us)
    (hind : fe.find? T = some (.indInfo cvT caps)) (hk : rl.k = true) :
    majorToCtorI mode r fe depth recName rules major
      = majorToCtorKClause mode r fe depth rl cvj cnP T major := by
  subst hrules
  rw [majorToCtorI, majorToCtorKClause]
  simp only [hctor, hfind, hhead, hind, hk, if_true]
  rfl

/-- The `rl.eta` clause. -/
theorem majorToCtorI_eq_eta {rules : List RecRule} {rl : RecRule} {cvj cvT : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us : List Level} {caps : IndCaps} {major : ExprC}
    (hctor : isCtorAppC fe major = false) (hrules : rules = [rl])
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T us)
    (hind : fe.find? T = some (.indInfo cvT caps)) (hk : rl.k = false)
    (heta : rl.eta = true) :
    majorToCtorI mode r fe depth recName rules major
      = majorToCtorEtaClause mode r fe depth rl cvT caps T major := by
  subst hrules
  rw [majorToCtorI, majorToCtorEtaClause]
  simp only [hctor, hfind, hhead, hind, hk, heta, Bool.false_eq_true, if_false, if_true]
  rfl

/-- The `And` clause. -/
theorem majorToCtorI_eq_and {rules : List RecRule} {rl : RecRule} {cvj cvT : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us : List Level} {caps : IndCaps} {major : ExprC}
    (hctor : isCtorAppC fe major = false) (hrules : rules = [rl])
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T us)
    (hind : fe.find? T = some (.indInfo cvT caps)) (hk : rl.k = false)
    (heta : rl.eta = false) (hand : T = andName) :
    majorToCtorI mode r fe depth recName rules major
      = majorToCtorAndClause mode r fe depth rl cvj cnP T major := by
  subst hrules; subst hand
  rw [majorToCtorI, majorToCtorAndClause]
  simp only [hctor, hfind, hhead, hind, hk, heta, if_true]
  rfl

/-! ### The five ways the dispatch stays stuck -/

theorem majorToCtorI_stuck_ctorApp {rules : List RecRule} {major : ExprC}
    (hctor : isCtorAppC fe major = true) :
    majorToCtorI mode r fe depth recName rules major = pure major := by
  rw [majorToCtorI.eq_def]; simp only [hctor, pure_bind, if_true]

theorem majorToCtorI_stuck_rules {rules : List RecRule} {major : ExprC}
    (hctor : isCtorAppC fe major = false) (hrules : rules.length ≠ 1) :
    majorToCtorI mode r fe depth recName rules major = pure major := by
  rw [majorToCtorI.eq_def]
  simp only [hctor, pure_bind, Bool.false_eq_true, if_false]
  match rules, hrules with
  | [], _ => rfl
  | [_], h => simp at h
  | _ :: _ :: _, _ => rfl

theorem majorToCtorI_stuck_ctor {rl : RecRule} {major : ExprC}
    (hctor : isCtorAppC fe major = false)
    (hfind : ∀ cv nP nF, fe.find? rl.ctor ≠ some (.ctorInfo cv nP nF)) :
    majorToCtorI mode r fe depth recName [rl] major = pure major := by
  rw [majorToCtorI]
  simp only [hctor]
  match hf : fe.find? rl.ctor with
  | none => rfl
  | some (.ctorInfo cv nP nF) => exact absurd hf (hfind cv nP nF)
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _ _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl

theorem majorToCtorI_stuck_head {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {major : ExprC} (hctor : isCtorAppC fe major = false)
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : ∀ T us, (cvj.type.piResult).getAppFn ≠ .const T us) :
    majorToCtorI mode r fe depth recName [rl] major = pure major := by
  rw [majorToCtorI]
  simp only [hctor, hfind]
  match hh : (cvj.type.piResult).getAppFn with
  | .const T us => exact absurd hh (hhead T us)
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem majorToCtorI_stuck_ind {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {T : Name} {us : List Level} {major : ExprC} (hctor : isCtorAppC fe major = false)
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T us)
    (hind : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    majorToCtorI mode r fe depth recName [rl] major = pure major := by
  rw [majorToCtorI]
  simp only [hctor, hfind, hhead]
  match hf : fe.find? T with
  | none => rfl
  | some (.indInfo cv caps) => exact absurd hf (hind cv caps)
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _ _)
  | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl

theorem majorToCtorI_stuck_bits {rl : RecRule} {cvj cvT : ConstantVal} {cnP cnF : Nat}
    {T : Name} {us : List Level} {caps : IndCaps} {major : ExprC}
    (hctor : isCtorAppC fe major = false)
    (hfind : fe.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T us)
    (hind : fe.find? T = some (.indInfo cvT caps)) (hk : rl.k = false)
    (heta : rl.eta = false) (hand : T ≠ andName) :
    majorToCtorI mode r fe depth recName [rl] major = pure major := by
  rw [majorToCtorI]
  simp only [hctor, hfind, hhead, hind, hk, heta, hand, Bool.false_eq_true, if_false]
  rfl

end Decompose

/-! ## The helpers that live in another arm's file

`proof_irrel_i`, `struct_eta_cert_with_i`, `iota_certs_i`, `proj_nodes_i` and
`proj_apps_i` are `Arms/Certs.lean`'s, `fab_scope_ok_i` is `Arms/App.lean`'s
and `infer_io_whnf_i` is `Arms/Shared.lean`'s.  Each field is that helper's own
`<fn>_refines`, quantified; the coordinator discharges the structure. -/

/-- The cross-file helpers the `major_to_ctor_*` group calls. -/
structure MajorDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `proof_irrel_i` (`core_c.rs:568`) refines `proofIrrelI`. -/
  proofIrrel : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True) (fun st fe => cached.core_c.proof_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.proofIrrelI (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b))
  /-- `struct_eta_cert_with_i` (`core_c.rs:839`) refines `structEtaCertWithI`. -/
  structEtaCertWith : ∀ (d : Std.U64) {a b wtb : expr.Expr}, ExprWF a → ExprWF b →
    ExprWF wtb →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_with_i mode fuel st fe d a b wtb)
      (fun lfe => ConLeche.Cached.structEtaCertWithI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b) (absExpr wtb))
  /-- `iota_certs_i` (`core_c.rs:415`) refines `iotaCertsI`. -/
  iotaCerts : ∀ (d : Std.U64) (lic : Bool) {ty : expr.Expr}
    {args : alloc.vec.Vec expr.Expr}, ExprWF ty → ExprsWF args →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i mode fuel st fe d lic ty args)
      (fun lfe => ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val lic
        (absExpr ty) (absExprs args))
  /-- `proj_nodes_i` (`core_c.rs:717`) refines `projNodesI`: the tower-node
  spelling, a state-free list.  Stated at the `j = 0`, `out = []` entry the
  `And` rescue calls it at. -/
  projNodes : ∀ {t : name.Name} {b : expr.Expr} {nf : Std.U64}
    {res : alloc.vec.Vec expr.Expr}, NameWF t → ExprWF b →
    cached.core_c.proj_nodes_i t b nf 0#u64 (alloc.vec.Vec.new expr.Expr) = ok res →
    (∀ lst, (ConLeche.Cached.projNodesI (absName t) (absExpr b)
        (List.range nf.val)).run lst = .ok (absExprs res, lst)) ∧ ExprsWF res
  /-- `proj_apps_i` (`core_c.rs:737`) refines `projAppsI` (the `Tn`/`T`
  collapse of task #18's deviation 4: one name argument, passed twice). -/
  projApps : ∀ {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {t : name.Name}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} {nf : Std.U64} {res : alloc.vec.Vec expr.Expr},
    FEnvWF fe → FEnvRel fe lfe → NameWF t → LevelsWF us → ExprsWF targs →
    ExprWF b → cached.core_c.proj_apps_i fe t us targs b nf = ok res →
    (∀ lst, (ConLeche.Cached.projAppsI lfe (absName t) (absName t) (absLevels us)
        (absExprs targs) (absExpr b) nf.val).run lst = .ok (absExprs res, lst)) ∧
      ExprsWF res
  /-- `fab_scope_ok_i` (`core_c.rs:1272`) refines the three-conjunct scope
  guard the three rescues run on their fabrication. -/
  fabScopeOk : ∀ {fab major : expr.Expr} {d : Std.U64} {c : Bool}, ExprWF fab →
    ExprWF major → cached.core_c.fab_scope_ok_i fab major d = ok c →
    c = (ConLeche.Cached.ExprC.wscopedB d.val (absExpr fab) &&
      ConLeche.Cached.ExprC.looseBVarsBounded 0 (absExpr fab) &&
      ConLeche.Cached.ExprC.leafGuard (absExpr fab) (absExpr major))
  /-- `infer_io_whnf_i` (`core_c.rs:1455`) refines
  `r.whnf depth (← r.inferIO depth e)`. -/
  inferIOWhnf : ∀ (d : Std.U64) {e : expr.Expr}, ExprWF e →
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_io_whnf_i mode fuel st fe d e)
      (fun lfe => do
        let t ← (knot mode lfe fuel.val).inferIO d.val (absExpr e)
        (knot mode lfe fuel.val).whnf d.val t)

/-! ## The monad plumbing

`Refine/StateC.lean`'s set, re-declared (an `attribute [local simp]` does not
cross a file boundary), plus the `Option`-free `run` of a `pure`. -/

/-- `pure` in `Except` is `ok`. -/
@[local simp] theorem except_pure'' {E A : Type} (a : A) :
    (pure a : Except E A) = .ok a := rfl

attribute [local simp] StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- **One `CheckCM` bind, run**: the step every arm's proof composes the `Sim`
run equations with.  `Refine/StateC.lean`'s run lemmas are per-branch for the
same reason — a state argument does not travel through a `match`. -/
theorem run_bind {α β : Type} {a : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst lst1 : ConLeche.Cached.CState} {x : α}
    (h : a.run lst = .ok (x, lst1)) : (a >>= f).run lst = (f x).run lst1 := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]; rfl

/-- **Two `CheckCM` binds, run at once**: `infer_io_whnf_i`'s Lean side is
`do let t ← r.inferIO …; r.whnf … t`, which the clauses spell out as two
`let`s — associativity is the whole of the difference. -/
theorem run_bind2 {α β γ : Type} {A : ConLeche.Cached.CheckCM α}
    {B : α → ConLeche.Cached.CheckCM β} {C : β → ConLeche.Cached.CheckCM γ}
    {lst lst2 : ConLeche.Cached.CState} {x : β}
    (h : (A >>= B).run lst = .ok (x, lst2)) :
    (A >>= fun a => B a >>= C).run lst = (C x).run lst2 := by
  rw [← bind_assoc]; exact run_bind h

/-- **Move 1 across the same two binds** (task #67): the error half of
`run_bind2`.  `infer_io_whnf_i` is one Rust call against con-leche's *two*
steps, so when it throws the error has to be carried past both. -/
theorem ErrSim.bindCM2 {α β γ : Type} {e : core_types.CheckError}
    {A : ConLeche.Cached.CheckCM α} {B : α → ConLeche.Cached.CheckCM β}
    {C : β → ConLeche.Cached.CheckCM γ} {lst : ConLeche.Cached.CState}
    (h : ErrSim e ((A >>= B).run lst)) :
    ErrSim e ((A >>= fun a => B a >>= C).run lst) := by
  rw [← bind_assoc]; exact ErrSim.bindCM h

/-- `pure`, run. -/
@[local simp] theorem run_pure {α : Type} (x : α) (lst : ConLeche.Cached.CState) :
    (pure x : ConLeche.Cached.CheckCM α).run lst = .ok (x, lst) := rfl

/-! ## The two literal conversions -/

section Literals
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `litToCtorIfNatI` *is* task #49's `litToCtorIfNatBody` under a `pure`:
`ConLeche/Cached/CoreC.lean:84-90` against `Refine/CoreKLits.lean:342`. -/
theorem litToCtorIfNatI_eq (lfe : ConLeche.FEnv) (e : ConLeche.Cached.ExprC) :
    ConLeche.Cached.litToCtorIfNatI lfe e
      = pure (litToCtorIfNatBody (ConLeche.natLitSupportedF lfe) e) := by
  match e with
  | .lit (.natVal _) =>
    simp only [ConLeche.Cached.litToCtorIfNatI, litToCtorIfNatBody]
    split <;> rfl
  | .lit (.strVal _) => rfl
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ => rfl

/-- The `litToCtorIfNatI` tail, run: `core_k::lit_to_ctor_if_nat` through
task #49's lemma and `litToCtorIfNatI_eq`. -/
private theorem lit_to_ctor_if_nat_run {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {e c : expr.Expr} (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe) (he : ExprWF e)
    (h : core_k.lit_to_ctor_if_nat fe e = ok c) (lst : ConLeche.Cached.CState) :
    (ConLeche.Cached.litToCtorIfNatI lfe (absExpr e)).run lst = .ok (absExpr c, lst)
      ∧ ExprWF c := by
  obtain ⟨habs, hcwf⟩ := CoreK.lit_to_ctor_if_nat_refines he
    (CoreK.natLitSupportedSpec (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe))
    CoreK.pinnedBasisNames.natZero CoreK.pinnedBasisNames.natSucc h
  refine ⟨?_, hcwf⟩
  rw [litToCtorIfNatI_eq, ← habs]
  simp

/-- `ConLeche/Cached/CoreC.lean:672` — **`lit_major_to_ctor_i` refines
`litMajorToCtorI`** (`core_c.rs:1656`): a `Nat` literal one layer
(`litToCtorIfNatI`), a `String` literal to its *reduced* constructor form
(`String.ofList` is a definition, so the fabrication is `whnf`'d). -/
theorem lit_major_to_ctor_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.lit_major_to_ctor_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.litMajorToCtorI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  have hc := ExprWF.children he
  obtain ⟨⟨dg, k⟩⟩ := e
  simp only [ExprOps.node_kind] at hc
  unfold cached.core_c.lit_major_to_ctor_i at hok
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
  cases k with
  | Lit l =>
    cases l with
    | NatVal n =>
      obtain ⟨c, hcl, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      obtain ⟨hrun, hcwf⟩ := lit_to_ctor_if_nat_run hfe hfrel he hcl lst
      exact ⟨lst, by simpa [ConLeche.Cached.litMajorToCtorI, absExprKind, absLiteral]
        using hrun, hrel, hwf, hcwf⟩
    | StrVal s =>
      have hsw : StrWF s := by simpa [LiteralWF] using hc
      obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
      have hbv := CoreK.strLitSupportedSpec (FindAgree.of_rel hfrel hfe)
        (FindWF.of_wf hfe) b hb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hok
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ⟨lst, by
          simp [ConLeche.Cached.litMajorToCtorI, absExprKind, absLiteral, ← hbv],
          hrel, hwf, he⟩
      | true =>
        simp only [if_true, bind_eq_ok_iff] at hok
        obtain ⟨cx, hcx, hok⟩ := hok
        obtain ⟨habs, hcxwf⟩ := CoreK.str_lit_to_constructor_refines hsw
          CoreK.pinnedBasisNames.char CoreK.pinnedBasisNames.charOfNat
          CoreK.pinnedBasisNames.listNil CoreK.pinnedBasisNames.listCons
          CoreK.pinnedBasisNames.stringOfList hcx
        cases oc with
        | Ok r =>
          obtain ⟨lst', hrun, hrel', hwf', hrwf⟩ :=
            (hw.whnfSim d hcxwf).apply hwf hfe hok hrel hfrel
          refine ⟨lst', ?_, hrel', hwf', hrwf⟩
          simp only [ConLeche.Cached.litMajorToCtorI, absExpr_mk, absExprKind, absLiteral,
            ← hbv, if_true]
          simpa [habs] using hrun
        | Err e =>
          -- the fabrication's `whnf` threw: con-leche's `r.whnf` is the same call
          refine Out.err (ErrSim.of_eq
            ((hw.whnfSim d hcxwf).apply_err hwf hfe hok hrel hfrel) ?_)
          simp only [ConLeche.Cached.litMajorToCtorI, absExpr_mk, absExprKind, absLiteral,
            ← hbv, if_true]
          simp [habs]
  | _ =>
    all_goals (
      obtain ⟨c, hcl, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      obtain ⟨hrun, hcwf⟩ := lit_to_ctor_if_nat_run hfe hfrel he hcl lst
      exact ⟨lst, by simpa [ConLeche.Cached.litMajorToCtorI, absExprKind] using hrun,
        hrel, hwf, hcwf⟩)

/-- `ConLeche/Cached/CoreC.lean:683` — **`proj_lit_to_ctor_i` refines
`projLitToCtorI`** (`core_c.rs:1683`): a `String` literal to its *reduced*
constructor form, everything else unchanged. -/
theorem proj_lit_to_ctor_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.proj_lit_to_ctor_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.projLitToCtorI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  have hc := ExprWF.children he
  obtain ⟨⟨dg, k⟩⟩ := e
  simp only [ExprOps.node_kind] at hc
  unfold cached.core_c.proj_lit_to_ctor_i at hok
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
  cases k with
  | Lit l =>
    cases l with
    | NatVal n =>
      obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hcd] at hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact ⟨lst, by simp [ConLeche.Cached.projLitToCtorI, absExprKind, absLiteral],
        hrel, hwf, he⟩
    | StrVal s =>
      have hsw : StrWF s := by simpa [LiteralWF] using hc
      obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
      have hbv := CoreK.strLitSupportedSpec (FindAgree.of_rel hfrel hfe)
        (FindWF.of_wf hfe) b hb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hok
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ⟨lst, by
          simp [ConLeche.Cached.projLitToCtorI, absExprKind, absLiteral, ← hbv],
          hrel, hwf, he⟩
      | true =>
        simp only [if_true, bind_eq_ok_iff] at hok
        obtain ⟨cx, hcx, hok⟩ := hok
        obtain ⟨habs, hcxwf⟩ := CoreK.str_lit_to_constructor_refines hsw
          CoreK.pinnedBasisNames.char CoreK.pinnedBasisNames.charOfNat
          CoreK.pinnedBasisNames.listNil CoreK.pinnedBasisNames.listCons
          CoreK.pinnedBasisNames.stringOfList hcx
        cases oc with
        | Ok r =>
          obtain ⟨lst', hrun, hrel', hwf', hrwf⟩ :=
            (hw.whnfSim d hcxwf).apply hwf hfe hok hrel hfrel
          refine ⟨lst', ?_, hrel', hwf', hrwf⟩
          simp only [ConLeche.Cached.projLitToCtorI, absExpr_mk, absExprKind, absLiteral,
            ← hbv, if_true]
          simpa [habs] using hrun
        | Err e =>
          refine Out.err (ErrSim.of_eq
            ((hw.whnfSim d hcxwf).apply_err hwf hfe hok hrel hfrel) ?_)
          simp only [ConLeche.Cached.projLitToCtorI, absExpr_mk, absExprKind, absLiteral,
            ← hbv, if_true]
          simp [habs]
  | _ =>
    all_goals (
      obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hcd] at hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact ⟨lst, by simp [ConLeche.Cached.projLitToCtorI, absExprKind], hrel, hwf, he⟩)

end Literals

/-! ## The two certificate tails -/

section Tails
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:589-596` — **`k_type_and_irrel_i` refines the
K arm's last two certificates** (`core_c.rs:1420`), shared with the `And` arm:
the fabrication's type against the major's (the official check, run in *both*
modes) and then proof irrelevance as the soundness certificate — a certificate
family, so `certAtI mode`. -/
theorem k_type_and_irrel_i_refines (hw : Wrappers mode fuel) (hd : MajorDeps mode fuel)
    (d : Std.U64) {tmaj fab major : expr.Expr} (htmaj : ExprWF tmaj) (hfab : ExprWF fab)
    (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.k_type_and_irrel_i mode fuel st fe d tmaj fab major)
      (fun lfe => kTypeAndIrrelTail (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr tmaj) (absExpr fab) (absExpr major)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.k_type_and_irrel_i at hok
  obtain ⟨⟨rio, st1⟩, hio, hok⟩ := bind_eq_ok_iff.mp hok
  cases rio with
  | Err e =>
    -- `r.inferIO depth fab`, the tail's first step, threw
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    simp only [kTypeAndIrrelTail]
    exact ErrSim.bindCM ((hw.inferIOSim d hfab).apply_err hwf hfe hio hrel hfrel)
  | Ok tfab =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htfab⟩ :=
      (hw.inferIOSim d hfab).apply hwf hfe hio hrel hfrel
    try dsimp only at hok
    obtain ⟨⟨rdq, st2⟩, hdq, hok⟩ := bind_eq_ok_iff.mp hok
    cases rdq with
    | Err e =>
      -- `r.defeq depth tmaj tfab` threw
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.err ?_
      simp only [kTypeAndIrrelTail]
      rw [run_bind hrun1]
      exact ErrSim.bindCM ((hw.defeqSim d htmaj htfab).apply_err hwf1 hfe hdq hrel1 hfrel)
    | Ok b =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
        (hw.defeqSim d htmaj htfab).apply hwf1 hfe hdq hrel1 hfrel
      try dsimp only at hok
      cases b with
      | false =>
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, hmajor⟩
        simp only [kTypeAndIrrelTail]
        rw [run_bind hrun1, run_bind hrun2]
        simp
      | true =>
        obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
        have hb1v := Env.certs_refines hb1
        cases b1 with
        | false =>
          try dsimp only at hok
          obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
          rw [← Result.ok_injective hp] at hok
          try dsimp only at hok
          obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
          rw [Expr.dup_eq hcd] at hok
          simp only [Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst2, ?_, hrel2, hwf2, hfab⟩
          simp only [kTypeAndIrrelTail]
          rw [run_bind hrun1, run_bind hrun2]
          simp only [id_eq, if_true, ConLeche.Cached.certAtI, ← hb1v,
            Bool.false_eq_true, if_false]
          simp
        | true =>
          try dsimp only at hok
          obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨⟨irrel, st4⟩, hpi, hp⟩ := bind_eq_ok_iff.mp hp
          rw [← Result.ok_injective hp] at hok
          try dsimp only at hok
          cases irrel with
          | Err e =>
            -- `proofIrrelI` under `certAtI` threw
            simp at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine Out.err ?_
            simp only [kTypeAndIrrelTail]
            rw [run_bind hrun1, run_bind hrun2]
            simp only [id_eq, if_true, ConLeche.Cached.certAtI, ← hb1v, if_true]
            exact ErrSim.bindCM
              ((hd.proofIrrel d hfab hmajor).apply_err hwf2 hfe hpi hrel2 hfrel)
          | Ok b2 =>
            obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
              (hd.proofIrrel d hfab hmajor).apply hwf2 hfe hpi hrel2 hfrel
            try dsimp only at hok
            cases b2 with
            | true =>
              obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
              rw [Expr.dup_eq hcd] at hok
              simp only [Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst3, ?_, hrel3, hwf3, hfab⟩
              simp only [kTypeAndIrrelTail]
              rw [run_bind hrun1, run_bind hrun2]
              simp only [id_eq, if_true, ConLeche.Cached.certAtI, ← hb1v, if_true]
              rw [run_bind hrun3]
              simp
            | false =>
              obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
              rw [Expr.dup_eq hcd] at hok
              simp only [Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst3, ?_, hrel3, hwf3, hmajor⟩
              simp only [kTypeAndIrrelTail]
              rw [run_bind hrun1, run_bind hrun2]
              simp only [id_eq, if_true, ConLeche.Cached.certAtI, ← hb1v, if_true]
              rw [run_bind hrun3]
              simp

/-- `ConLeche/Cached/CoreC.lean:628-635` — **`eta_rescue_certs_i` refines the η
arm's certificate** (`core_c.rs:1551`): the structure-eta certificate against
the major's own reduced type, with the **0-field rescue** behind it (the
generic certificate excludes reserved names; the fabrication is the bare
constructor, certified by proof irrelevance's unit-likeness branch). -/
theorem eta_rescue_certs_i_refines (hd : MajorDeps mode fuel) (d : Std.U64)
    {fab major tmaj : expr.Expr} (caps : env.IndCaps) (hfab : ExprWF fab)
    (hmajor : ExprWF major) (htmaj : ExprWF tmaj) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.eta_rescue_certs_i mode fuel st fe d fab major tmaj caps)
      (fun lfe => etaRescueCertsTail (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr fab) (absExpr major) (absExpr tmaj) (absIndCaps caps)) := by
  have hef : (absIndCaps caps).etaFields = caps.eta_fields.val := rfl
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.eta_rescue_certs_i at hok
  obtain ⟨⟨rc, st1⟩, hc, hok⟩ := bind_eq_ok_iff.mp hok
  cases rc with
  | Err e =>
    -- `structEtaCertWithI`, the tail's first step, threw
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    simp only [etaRescueCertsTail]
    exact ErrSim.bindCM
      ((hd.structEtaCertWith d hfab hmajor htmaj).apply_err hwf hfe hc hrel hfrel)
  | Ok b =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
      (hd.structEtaCertWith d hfab hmajor htmaj).apply hwf hfe hc hrel hfrel
    try dsimp only at hok
    cases b with
    | true =>
      obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hcd] at hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine ⟨lst1, ?_, hrel1, hwf1, hfab⟩
      simp only [etaRescueCertsTail]
      rw [run_bind hrun1]
      simp
    | false =>
      by_cases hz : caps.eta_fields = 0#u64
      · simp only [hz, reduceIte] at hok
        obtain ⟨⟨rpi, st2⟩, hpi, hok⟩ := bind_eq_ok_iff.mp hok
        cases rpi with
        | Err e =>
          -- the 0-field `proofIrrelI` rescue threw
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          have hz' : (absIndCaps caps).etaFields = 0 := by rw [hef, hz]; rfl
          refine Out.err ?_
          simp only [etaRescueCertsTail]
          rw [run_bind hrun1]
          simp only [id_eq, Bool.false_eq_true, if_false, hz', if_true]
          exact ErrSim.bindCM
            ((hd.proofIrrel d hfab hmajor).apply_err hwf1 hfe hpi hrel1 hfrel)
        | Ok b1 =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
            (hd.proofIrrel d hfab hmajor).apply hwf1 hfe hpi hrel1 hfrel
          have hz' : (absIndCaps caps).etaFields = 0 := by rw [hef, hz]; rfl
          try dsimp only at hok
          cases b1 with
          | true =>
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst2, ?_, hrel2, hwf2, hfab⟩
            simp only [etaRescueCertsTail]
            rw [run_bind hrun1]
            simp only [id_eq, Bool.false_eq_true, if_false, hz', if_true]
            rw [run_bind hrun2]
            simp
          | false =>
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst2, ?_, hrel2, hwf2, hmajor⟩
            simp only [etaRescueCertsTail]
            rw [run_bind hrun1]
            simp only [id_eq, Bool.false_eq_true, if_false, hz', if_true]
            rw [run_bind hrun2]
            simp
      · simp only [if_neg hz] at hok
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        have hz' : ¬ ((absIndCaps caps).etaFields = 0) := by
          rw [hef]; intro h; exact hz (by scalar_tac)
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [etaRescueCertsTail]
        rw [run_bind hrun1]
        simp only [id_eq, Bool.false_eq_true, if_false, if_neg hz']
        simp

end Tails

/-! ## The three rescue arms -/

section Arms
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:556-598` — **`major_to_ctor_k_i` refines the
`rl.k` clause** of `majorToCtorI` (`core_c.rs:1354`). -/
theorem major_to_ctor_k_i_refines (hw : Wrappers mode fuel) (hd : MajorDeps mode fuel)
    (d : Std.U64) {rl : env.RecRule} {cvj : env.ConstantVal} (cn_p : Std.U64)
    {t : name.Name} {major : expr.Expr} (hrl : RecRuleWF rl) (_hcvj : ConstantValWF cvj)
    (ht : NameWF t) (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.major_to_ctor_k_i mode fuel st fe d rl cvj cn_p t major)
      (fun lfe => majorToCtorKClause (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absRecRule rl) (absConstantVal cvj) cn_p.val (absName t) (absExpr major)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.major_to_ctor_k_i at hok
  obtain ⟨⟨riw, st1⟩, hiw, hok⟩ := bind_eq_ok_iff.mp hok
  cases riw with
  | Err e =>
    -- the clause's first two steps, `r.whnf depth (← r.inferIO depth major)`, threw
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    simp only [majorToCtorKClause]
    exact ErrSim.bindCM2 ((hd.inferIOWhnf d hmajor).apply_err hwf hfe hiw hrel hfrel)
  | Ok tmaj =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htmaj⟩ :=
      (hd.inferIOWhnf d hmajor).apply hwf hfe hiw hrel hfrel
    obtain ⟨head, hhd, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines htmaj hhd
    simp only [arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨⟨dh, kh⟩⟩ := head
    simp only [ExprOps.node_kind] at hok
    simp only [absExpr_mk] at hhabs
    cases kh with
    | Const t2 ust =>
      obtain ⟨ht2, hust⟩ := CoreK.wf_const_inv hhwf rfl
      have hhead : ConLeche.Cached.ExprC.getAppFn (absExpr tmaj)
          = ConLeche.Expr.const (absName t2) (absLevels ust) := by
        rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]; simp [absExprKind]
      obtain ⟨targs, hta, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨htaabs, htawf⟩ := ExprOps.get_app_args_refines htmaj hta
      have hargs : ConLeche.Cached.ExprC.getAppArgs (absExpr tmaj) = absExprs targs := by
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← htaabs]
      obtain ⟨bq, hbq, hok⟩ := bind_eq_ok_iff.mp hok
      have hbqv := Name.beq_refines ht2 ht hbq
      try simp only [arc_deref_eq, bind_tc_ok] at hok
      cases bq with
      | false =>
        have hne : ¬ (absName t2 = absName t) := by
          intro h; rw [h] at hbqv; simp at hbqv
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorKClause]
        rw [run_bind2 hrun1, hhead]
        simp only [pure_bind, beq_iff_eq, hne, false_and, if_false]
        simp
      | true =>
        have heq : absName t2 = absName t := by
          have h' : decide (absName t2 = absName t) = true := hbqv.symm
          simpa using h'
        have hlenl : (absConstantVal cvj).levelParams.length = cvj.level_params.val.length := by
          simp [absConstantVal, absNames]
        have hlenu : (absLevels ust).length = ust.val.length := by simp [absLevels]
        have hlena : (absExprs targs).length = targs.val.length := by simp [absExprs]
        by_cases hlen : alloc.vec.Vec.len cvj.level_params = alloc.vec.Vec.len ust
        case neg =>
          -- the level-parameter counts differ: stuck
          rw [if_pos (bne_iff_ne.mpr hlen)] at hok
          have hlen' : ¬ ((absConstantVal cvj).levelParams.length = (absLevels ust).length) := by
            rw [hlenl, hlenu]
            have h1 := alloc.vec.Vec.len_val cvj.level_params
            have h2 := alloc.vec.Vec.len_val ust
            intro hc; exact hlen (by scalar_tac)
          obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
          rw [Expr.dup_eq hcd] at hok
          simp only [Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
          simp only [majorToCtorKClause]
          rw [run_bind2 hrun1, hhead]
          simp only [pure_bind]
          rw [if_neg (fun hc => hlen' hc.2)]
          simp
        case pos =>
          have hcond : ¬ ((alloc.vec.Vec.len cvj.level_params
              != alloc.vec.Vec.len ust) = true) := by
            simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hlen
          rw [if_neg hcond] at hok
          have hlenE : (absConstantVal cvj).levelParams.length = (absLevels ust).length := by
            rw [hlenl, hlenu]
            have h1 := alloc.vec.Vec.len_val cvj.level_params
            have h2 := alloc.vec.Vec.len_val ust
            scalar_tac
          have hc1 : ((absName t2 == absName t) = true ∧
              (absConstantVal cvj).levelParams.length = (absLevels ust).length) :=
            ⟨by rw [heq]; simp, hlenE⟩
          obtain ⟨i3, hi3, hok⟩ := bind_eq_ok_iff.mp hok
          have hi3v : i3.val = targs.val.length := by
            simp only [lift_eq, Result.ok.injEq] at hi3
            rw [← hi3, ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
          by_cases hgt : cn_p > i3
          case pos =>
            -- fewer arguments than the constructor has parameters: stuck
            rw [if_pos hgt] at hok
            have hgt' : ¬ (cn_p.val ≤ (absExprs targs).length) := by
              rw [hlena, ← hi3v]; scalar_tac
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
            simp only [majorToCtorKClause]
            rw [run_bind2 hrun1, hhead]
            simp only [pure_bind]
            rw [if_pos hc1, hargs, if_neg hgt']
            simp
          case neg =>
            rw [if_neg hgt] at hok
            have hle : cn_p.val ≤ (absExprs targs).length := by
              rw [hlena, ← hi3v]; scalar_tac
            obtain ⟨params, hpa, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨hpabs, hpwf⟩ := CoreK.take_exprs_n_refines htawf hpa
            obtain ⟨nn, hnn, hok⟩ := bind_eq_ok_iff.mp hok
            rw [name_dup_eq] at hnn
            have hnnv : nn = rl.ctor := (Result.ok_injective hnn).symm
            subst hnnv
            obtain ⟨v1, hv1, hok⟩ := bind_eq_ok_iff.mp hok
            have hv1v : v1 = ust := Env.levels_copy_refines hv1
            subst hv1v
            obtain ⟨hh, hhc, hok⟩ := bind_eq_ok_iff.mp hok
            have hhabs2 : absExpr hh
                = ConLeche.Expr.const (absName rl.ctor) (absLevels v1) :=
              Expr.mk_const_refines hhc
            have hhwf2 : ExprWF hh := Expr.mk_const_wf hrl.1 hust hhc
            obtain ⟨fab, hfb, hok⟩ := bind_eq_ok_iff.mp hok
            rw [StateC.mk_app_n_m_eq] at hfb
            obtain ⟨hfabs, hfabwf⟩ := ExprOpsC.mk_app_n_refines hhwf2 hpwf hfb
            rw [hhabs2, hpabs] at hfabs
            have hfabL : ConLeche.Cached.ExprC.mkAppN
                (ConLeche.Expr.const (absRecRule rl).ctor (absLevels v1))
                (List.take cn_p.val (absExprs targs)) = absExpr fab := hfabs.symm
            obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
            have hb1v := hd.fabScopeOk hfabwf hmajor hb1
            cases b1 with
            | false =>
              obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
              rw [Expr.dup_eq hcd] at hok
              simp only [Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
              simp only [majorToCtorKClause]
              rw [run_bind2 hrun1, hhead]
              simp only [pure_bind]
              rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
              simp only [pure_bind]
              rw [hfabL, ← hb1v]
              simp
            | true =>
              -- `const_ty_at_m` is read *outside* the `certs` gate, exactly where
              -- `ConLeche/Cached/CoreC.lean:574` has `constTyAtM` (task #61), so
              -- both modes move the memo table the same way and the mode split
              -- happens after it.
              obtain ⟨⟨rcty, st2⟩, hcty, hok⟩ := bind_eq_ok_iff.mp hok
              cases rcty with
              | Err e =>
                -- the certificate read itself threw, in both modes
                simp at hok
                obtain ⟨rfl, rfl⟩ := hok
                refine Out.err ?_
                simp only [majorToCtorKClause]
                rw [run_bind2 hrun1, hhead]
                simp only [pure_bind]
                rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                simp only [pure_bind]
                rw [hfabL, ← hb1v]
                simp only [if_true]
                exact ErrSim.bindCM (StateC.const_ty_at_m_err hwf1 hfe hrl.1 hust hcty
                  lst1 lfe hrel1 hfrel (absRecRule rl).ctor)
              | Ok cty =>
                obtain ⟨lstc, hrunc, hrelc, hwfc, hctywf⟩ :=
                  StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf1 hfe
                    hrl.1 hust hcty lst1 lfe hrel1 hfrel (absRecRule rl).ctor
                have hruncL : (ConLeche.Cached.constTyAtM lfe (absRecRule rl).ctor
                    (absRecRule rl).ctor (absLevels v1)).run lst1
                    = .ok (absExpr cty, lstc) := hrunc
                try dsimp only at hok
                obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨b2, hb2, hp⟩ := bind_eq_ok_iff.mp hp
                have hb2v := Env.certs_refines hb2
                cases b2 with
                | false =>
                  rw [← Result.ok_injective hp] at hok
                  try dsimp only at hok
                  cases oc with
                  | Ok r =>
                    obtain ⟨lstk, hrunk, hrelk, hwfk, hrwf⟩ :=
                      (k_type_and_irrel_i_refines hw hd d htmaj hfabwf hmajor).apply
                        hwfc hfe hok hrelc hfrel
                    refine ⟨lstk, ?_, hrelk, hwfk, hrwf⟩
                    simp only [majorToCtorKClause]
                    rw [run_bind2 hrun1, hhead]
                    simp only [pure_bind]
                    rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                    simp only [pure_bind]
                    rw [hfabL, ← hb1v]
                    simp only [if_true]
                    rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                    simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                    exact hrunk
                  | Err e =>
                    refine Out.err ?_
                    simp only [majorToCtorKClause]
                    rw [run_bind2 hrun1, hhead]
                    simp only [pure_bind]
                    rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                    simp only [pure_bind]
                    rw [hfabL, ← hb1v]
                    simp only [if_true]
                    rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                    simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                    exact (k_type_and_irrel_i_refines hw hd d htmaj hfabwf hmajor).apply_err
                      hwfc hfe hok hrelc hfrel
                | true =>
                  try dsimp only at hp
                  obtain ⟨⟨rcert, st4⟩, hic, hp⟩ := bind_eq_ok_iff.mp hp
                  rw [← Result.ok_injective hp] at hok
                  try dsimp only at hok
                  cases rcert with
                  | Err e =>
                    -- `iotaCertsI` under `certAtI` threw
                    simp at hok
                    obtain ⟨rfl, rfl⟩ := hok
                    have hicerr := (hd.iotaCerts d false hctywf hpwf).apply_err
                      hwfc hfe hic hrelc hfrel
                    rw [hpabs] at hicerr
                    refine Out.err ?_
                    simp only [majorToCtorKClause]
                    rw [run_bind2 hrun1, hhead]
                    simp only [pure_bind]
                    rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                    simp only [pure_bind]
                    rw [hfabL, ← hb1v]
                    simp only [if_true]
                    rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                    simp only [reduceIte]
                    exact ErrSim.bindCM hicerr
                  | Ok b3 =>
                    obtain ⟨lsti, hruni, hreli, hwfi, -⟩ :=
                      (hd.iotaCerts d false hctywf hpwf).apply hwfc hfe hic hrelc hfrel
                    rw [hpabs] at hruni
                    cases b3 with
                    | false =>
                      obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                      rw [Expr.dup_eq hcd] at hok
                      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                      obtain ⟨rfl, rfl⟩ := hok
                      refine ⟨lsti, ?_, hreli, hwfi, hmajor⟩
                      simp only [majorToCtorKClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                      simp only [pure_bind]
                      rw [hfabL, ← hb1v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                      simp only [reduceIte]
                      rw [run_bind hruni]
                      simp
                    | true =>
                      cases oc with
                      | Ok r =>
                        obtain ⟨lstk, hrunk, hrelk, hwfk, hrwf⟩ :=
                          (k_type_and_irrel_i_refines hw hd d htmaj hfabwf hmajor).apply
                            hwfi hfe hok hreli hfrel
                        refine ⟨lstk, ?_, hrelk, hwfk, hrwf⟩
                        simp only [majorToCtorKClause]
                        rw [run_bind2 hrun1, hhead]
                        simp only [pure_bind]
                        rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                        simp only [pure_bind]
                        rw [hfabL, ← hb1v]
                        simp only [if_true]
                        rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                        simp only [reduceIte]
                        rw [run_bind hruni]
                        simp only [id_eq, if_true]
                        exact hrunk
                      | Err e =>
                        refine Out.err ?_
                        simp only [majorToCtorKClause]
                        rw [run_bind2 hrun1, hhead]
                        simp only [pure_bind]
                        rw [if_pos hc1, hargs, if_pos hle, ConLeche.Cached.mkAppNM]
                        simp only [pure_bind]
                        rw [hfabL, ← hb1v]
                        simp only [if_true]
                        rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                        simp only [reduceIte]
                        rw [run_bind hruni]
                        simp only [id_eq, if_true]
                        exact (k_type_and_irrel_i_refines hw hd d htmaj hfabwf
                          hmajor).apply_err hwfi hfe hok hreli hfrel
    | _ =>
      all_goals (
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorKClause]
        rw [run_bind2 hrun1, ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]
        simp [absExprKind])

/-- `ConLeche/Cached/CoreC.lean:638-666` — **`major_to_ctor_and_i` refines the
`And` clause** of `majorToCtorI` (`core_c.rs:1585`): `And.rec F h` at a stuck
PROOF `h` fires through the fabrication `And.intro a b (.proj And 0 h)
(.proj And 1 h)`, certified the K branch's way. -/
theorem major_to_ctor_and_i_refines (hw : Wrappers mode fuel) (hd : MajorDeps mode fuel)
    (d : Std.U64) {rl : env.RecRule} {cvj : env.ConstantVal} (cn_p : Std.U64)
    {t : name.Name} {major : expr.Expr} (hrl : RecRuleWF rl) (_hcvj : ConstantValWF cvj)
    (ht : NameWF t) (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.major_to_ctor_and_i mode fuel st fe d rl cvj cn_p t major)
      (fun lfe => majorToCtorAndClause (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absRecRule rl) (absConstantVal cvj) cn_p.val (absName t) (absExpr major)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.major_to_ctor_and_i at hok
  obtain ⟨⟨riw, st1⟩, hiw, hok⟩ := bind_eq_ok_iff.mp hok
  cases riw with
  | Err e =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    simp only [majorToCtorAndClause]
    exact ErrSim.bindCM2 ((hd.inferIOWhnf d hmajor).apply_err hwf hfe hiw hrel hfrel)
  | Ok tmaj =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htmaj⟩ :=
      (hd.inferIOWhnf d hmajor).apply hwf hfe hiw hrel hfrel
    obtain ⟨head, hhd, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines htmaj hhd
    simp only [arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨⟨dh, kh⟩⟩ := head
    simp only [ExprOps.node_kind] at hok
    simp only [absExpr_mk] at hhabs
    cases kh with
    | Const t2 ust =>
      obtain ⟨ht2, hust⟩ := CoreK.wf_const_inv hhwf rfl
      have hhead : ConLeche.Cached.ExprC.getAppFn (absExpr tmaj)
          = ConLeche.Expr.const (absName t2) (absLevels ust) := by
        rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]; simp [absExprKind]
      obtain ⟨targs, hta, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨htaabs, htawf⟩ := ExprOps.get_app_args_refines htmaj hta
      have hargs : ConLeche.Cached.ExprC.getAppArgs (absExpr tmaj) = absExprs targs := by
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← htaabs]
      obtain ⟨bq, hbq, hok⟩ := bind_eq_ok_iff.mp hok
      have hbqv := Name.beq_refines ht2 ht hbq
      try simp only [arc_deref_eq, bind_tc_ok] at hok
      have hlenl : (absConstantVal cvj).levelParams.length = cvj.level_params.val.length := by
        simp [absConstantVal, absNames]
      have hlenu : (absLevels ust).length = ust.val.length := by simp [absLevels]
      have hlena : (absExprs targs).length = targs.val.length := by simp [absExprs]
      cases bq with
      | false =>
        have hne : ¬ (absName t2 = absName t) := by
          intro h; rw [h] at hbqv; simp at hbqv
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorAndClause]
        rw [run_bind2 hrun1, hhead]
        simp only [pure_bind, beq_iff_eq, hne, false_and, if_false]
        simp
      | true =>
        have heq : absName t2 = absName t := by
          have h' : decide (absName t2 = absName t) = true := hbqv.symm
          simpa using h'
        obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
        have hi1v : i1.val = targs.val.length := by
          simp only [lift_eq, Result.ok.injEq] at hi1
          rw [← hi1, ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        by_cases hnp : i1 = cn_p
        case neg =>
          rw [if_pos (bne_iff_ne.mpr hnp)] at hok
          have hnp' : ¬ ((absExprs targs).length = cn_p.val) := by
            rw [hlena, ← hi1v]; intro hc; exact hnp (by scalar_tac)
          obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
          rw [Expr.dup_eq hcd] at hok
          simp only [Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
          simp only [majorToCtorAndClause]
          rw [run_bind2 hrun1, hhead]
          simp only [pure_bind]
          rw [hargs, if_neg (fun hc => hnp' hc.2.1)]
          simp
        case pos =>
          have hcond1 : ¬ ((i1 != cn_p) = true) := by
            simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hnp
          rw [if_neg hcond1] at hok
          have hnpE : (absExprs targs).length = cn_p.val := by
            rw [hlena, ← hi1v]; scalar_tac
          by_cases hlen : alloc.vec.Vec.len cvj.level_params = alloc.vec.Vec.len ust
          case neg =>
            rw [if_pos (bne_iff_ne.mpr hlen)] at hok
            have hlen' : ¬ ((absConstantVal cvj).levelParams.length
                = (absLevels ust).length) := by
              rw [hlenl, hlenu]
              have h1 := alloc.vec.Vec.len_val cvj.level_params
              have h2 := alloc.vec.Vec.len_val ust
              intro hc; exact hlen (by scalar_tac)
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
            simp only [majorToCtorAndClause]
            rw [run_bind2 hrun1, hhead]
            simp only [pure_bind]
            rw [hargs, if_neg (fun hc => hlen' hc.2.2.1)]
            simp
          case pos =>
            have hcond2 : ¬ ((alloc.vec.Vec.len cvj.level_params
                != alloc.vec.Vec.len ust) = true) := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hlen
            rw [if_neg hcond2] at hok
            have hlenE : (absConstantVal cvj).levelParams.length = (absLevels ust).length := by
              rw [hlenl, hlenu]
              have h1 := alloc.vec.Vec.len_val cvj.level_params
              have h2 := alloc.vec.Vec.len_val ust
              scalar_tac
            obtain ⟨bs, hbs, hok⟩ := bind_eq_ok_iff.mp hok
            have hbsv := CoreK.and_rescue_slots_refines CoreK.pinned_and_name
              (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hrl.1 hust hbs
            cases bs with
            | false =>
              obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
              rw [Expr.dup_eq hcd] at hok
              simp only [Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
              simp only [majorToCtorAndClause]
              rw [run_bind2 hrun1, hhead]
              simp only [pure_bind]
              rw [hargs, if_neg (fun hc => by
                have := hc.2.2.2
                rw [show ((absRecRule rl).ctor : ConLeche.Name) = absName rl.ctor from rfl,
                  ← hbsv] at this
                simp at this)]
              simp
            | true =>
              have hslots : ConLeche.FEnv.andRescueSlotsF lfe (absRecRule rl).ctor cn_p.val
                  (absLevels ust) = true := hbsv.symm
              have hc1 : ((absName t2 == absName t) = true ∧
                  (absExprs targs).length = cn_p.val ∧
                  (absConstantVal cvj).levelParams.length = (absLevels ust).length ∧
                  ConLeche.FEnv.andRescueSlotsF lfe (absRecRule rl).ctor cn_p.val
                    (absLevels ust) = true) :=
                ⟨by rw [heq]; simp, hnpE, hlenE, hslots⟩
              obtain ⟨projs, hpj, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨hpjrun, hpjwf⟩ := hd.projNodes ht hmajor hpj
              have hpjL : ∀ lz, (ConLeche.Cached.projNodesI (absName t) (absExpr major)
                  [0, 1]).run lz = .ok (absExprs projs, lz) := by
                intro lz
                have h := hpjrun lz
                rwa [show (List.range (2#u64 : Std.U64).val) = ([0, 1] : List Nat) from rfl] at h
              obtain ⟨tc, htc, hok⟩ := bind_eq_ok_iff.mp hok
              have htcv : tc = targs := Env.exprs_copy_refines htc
              obtain ⟨spine, hsp, hok⟩ := bind_eq_ok_iff.mp hok
              rw [htcv] at hsp
              obtain ⟨hspabs, hspwf⟩ := CoreK.append_exprs_refines htawf hpjwf hsp
              obtain ⟨nn, hnn, hok⟩ := bind_eq_ok_iff.mp hok
              rw [name_dup_eq] at hnn
              have hnnv : nn = rl.ctor := (Result.ok_injective hnn).symm
              subst hnnv
              obtain ⟨v1, hv1, hok⟩ := bind_eq_ok_iff.mp hok
              have hv1v : v1 = ust := Env.levels_copy_refines hv1
              subst hv1v
              obtain ⟨hh, hhc, hok⟩ := bind_eq_ok_iff.mp hok
              have hhabs2 : absExpr hh
                  = ConLeche.Expr.const (absName rl.ctor) (absLevels v1) :=
                Expr.mk_const_refines hhc
              have hhwf2 : ExprWF hh := Expr.mk_const_wf hrl.1 hust hhc
              obtain ⟨fab, hfb, hok⟩ := bind_eq_ok_iff.mp hok
              rw [StateC.mk_app_n_m_eq] at hfb
              obtain ⟨hfabs, hfabwf⟩ := ExprOpsC.mk_app_n_refines hhwf2 hspwf hfb
              rw [hhabs2, hspabs] at hfabs
              have hfabL : ConLeche.Cached.ExprC.mkAppN
                  (ConLeche.Expr.const (absRecRule rl).ctor (absLevels v1))
                  (absExprs targs ++ absExprs projs) = absExpr fab := hfabs.symm
              obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
              have hb1v := hd.fabScopeOk hfabwf hmajor hb1
              cases b1 with
              | false =>
                obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                rw [Expr.dup_eq hcd] at hok
                simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
                simp only [majorToCtorAndClause]
                rw [run_bind2 hrun1, hhead]
                simp only [pure_bind]
                rw [hargs, if_pos hc1]
                rw [run_bind (hpjL lst1)]
                simp only [ConLeche.Cached.mkAppNM, pure_bind]
                rw [hfabL, ← hb1v]
                simp
              | true =>
                -- `const_ty_at_m` is read *outside* the `certs` gate, exactly where
                -- `ConLeche/Cached/CoreC.lean:653` has `constTyAtM` (task #61), so
                -- both modes move the memo table the same way.
                obtain ⟨⟨rcty, st2⟩, hcty, hok⟩ := bind_eq_ok_iff.mp hok
                cases rcty with
                | Err e =>
                  simp at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine Out.err ?_
                  simp only [majorToCtorAndClause]
                  rw [run_bind2 hrun1, hhead]
                  simp only [pure_bind]
                  rw [hargs, if_pos hc1]
                  rw [run_bind (hpjL lst1)]
                  simp only [ConLeche.Cached.mkAppNM, pure_bind]
                  rw [hfabL, ← hb1v]
                  simp only [if_true]
                  exact ErrSim.bindCM (StateC.const_ty_at_m_err hwf1 hfe hrl.1 hust hcty
                    lst1 lfe hrel1 hfrel (absRecRule rl).ctor)
                | Ok cty =>
                  obtain ⟨lstc, hrunc, hrelc, hwfc, hctywf⟩ :=
                    StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf1 hfe
                      hrl.1 hust hcty lst1 lfe hrel1 hfrel (absRecRule rl).ctor
                  have hruncL : (ConLeche.Cached.constTyAtM lfe (absRecRule rl).ctor
                      (absRecRule rl).ctor (absLevels v1)).run lst1
                      = .ok (absExpr cty, lstc) := hrunc
                  try dsimp only at hok
                  obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
                  obtain ⟨b2, hb2, hp⟩ := bind_eq_ok_iff.mp hp
                  have hb2v := Env.certs_refines hb2
                  cases b2 with
                  | false =>
                    rw [← Result.ok_injective hp] at hok
                    try dsimp only at hok
                    cases oc with
                    | Ok r =>
                      obtain ⟨lstk, hrunk, hrelk, hwfk, hrwf⟩ :=
                        (k_type_and_irrel_i_refines hw hd d htmaj hfabwf hmajor).apply
                          hwfc hfe hok hrelc hfrel
                      refine ⟨lstk, ?_, hrelk, hwfk, hrwf⟩
                      simp only [majorToCtorAndClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1]
                      rw [run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb1v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                      simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                      exact hrunk
                    | Err e =>
                      refine Out.err ?_
                      simp only [majorToCtorAndClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1]
                      rw [run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb1v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                      simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                      exact (k_type_and_irrel_i_refines hw hd d htmaj hfabwf
                        hmajor).apply_err hwfc hfe hok hrelc hfrel
                  | true =>
                    try dsimp only at hp
                    obtain ⟨⟨rcert, st4⟩, hic, hp⟩ := bind_eq_ok_iff.mp hp
                    rw [← Result.ok_injective hp] at hok
                    try dsimp only at hok
                    cases rcert with
                    | Err e =>
                      simp at hok
                      obtain ⟨rfl, rfl⟩ := hok
                      have hicerr := (hd.iotaCerts d false hctywf hspwf).apply_err
                        hwfc hfe hic hrelc hfrel
                      rw [hspabs] at hicerr
                      refine Out.err ?_
                      simp only [majorToCtorAndClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1]
                      rw [run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb1v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                      simp only [reduceIte]
                      exact ErrSim.bindCM hicerr
                    | Ok b3 =>
                      obtain ⟨lsti, hruni, hreli, hwfi, -⟩ :=
                        (hd.iotaCerts d false hctywf hspwf).apply hwfc hfe hic hrelc hfrel
                      rw [hspabs] at hruni
                      cases b3 with
                      | false =>
                        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                        rw [Expr.dup_eq hcd] at hok
                        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                        obtain ⟨rfl, rfl⟩ := hok
                        refine ⟨lsti, ?_, hreli, hwfi, hmajor⟩
                        simp only [majorToCtorAndClause]
                        rw [run_bind2 hrun1, hhead]
                        simp only [pure_bind]
                        rw [hargs, if_pos hc1]
                        rw [run_bind (hpjL lst1)]
                        simp only [ConLeche.Cached.mkAppNM, pure_bind]
                        rw [hfabL, ← hb1v]
                        simp only [if_true]
                        rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                        simp only [reduceIte]
                        rw [run_bind hruni]
                        simp
                      | true =>
                        cases oc with
                        | Ok r =>
                          obtain ⟨lstk, hrunk, hrelk, hwfk, hrwf⟩ :=
                            (k_type_and_irrel_i_refines hw hd d htmaj hfabwf hmajor).apply
                              hwfi hfe hok hreli hfrel
                          refine ⟨lstk, ?_, hrelk, hwfk, hrwf⟩
                          simp only [majorToCtorAndClause]
                          rw [run_bind2 hrun1, hhead]
                          simp only [pure_bind]
                          rw [hargs, if_pos hc1]
                          rw [run_bind (hpjL lst1)]
                          simp only [ConLeche.Cached.mkAppNM, pure_bind]
                          rw [hfabL, ← hb1v]
                          simp only [if_true]
                          rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                          simp only [reduceIte]
                          rw [run_bind hruni]
                          simp only [id_eq, if_true]
                          exact hrunk
                        | Err e =>
                          refine Out.err ?_
                          simp only [majorToCtorAndClause]
                          rw [run_bind2 hrun1, hhead]
                          simp only [pure_bind]
                          rw [hargs, if_pos hc1]
                          rw [run_bind (hpjL lst1)]
                          simp only [ConLeche.Cached.mkAppNM, pure_bind]
                          rw [hfabL, ← hb1v]
                          simp only [if_true]
                          rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb2v]
                          simp only [reduceIte]
                          rw [run_bind hruni]
                          simp only [id_eq, if_true]
                          exact (k_type_and_irrel_i_refines hw hd d htmaj hfabwf
                            hmajor).apply_err hwfi hfe hok hreli hfrel
    | _ =>
      all_goals (
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorAndClause]
        rw [run_bind2 hrun1, ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]
        simp [absExprKind])

/-- `ConLeche/Cached/CoreC.lean:599-637` — **`major_to_ctor_eta_i` refines the
`rl.eta` clause** of `majorToCtorI` (`core_c.rs:1477`): for an eta-capable
structure the constructor of the major's projections is fabricated
(`projAppsI`) and certified by the structure-eta certificate. -/
theorem major_to_ctor_eta_i_refines (hd : MajorDeps mode fuel) (d : Std.U64)
    {rl : env.RecRule} {cvt : env.ConstantVal} {caps : env.IndCaps}
    {t : name.Name} {major : expr.Expr} (hrl : RecRuleWF rl) (hcvt : ConstantValWF cvt)
    (hcaps : IndCapsWF caps) (ht : NameWF t) (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.major_to_ctor_eta_i mode fuel st fe d rl cvt caps t major)
      (fun lfe => majorToCtorEtaClause (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absRecRule rl) (absConstantVal cvt) (absIndCaps caps) (absName t)
        (absExpr major)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.major_to_ctor_eta_i at hok
  obtain ⟨⟨riw, st1⟩, hiw, hok⟩ := bind_eq_ok_iff.mp hok
  cases riw with
  | Err e =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    simp only [majorToCtorEtaClause]
    exact ErrSim.bindCM2 ((hd.inferIOWhnf d hmajor).apply_err hwf hfe hiw hrel hfrel)
  | Ok tmaj =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htmaj⟩ :=
      (hd.inferIOWhnf d hmajor).apply hwf hfe hiw hrel hfrel
    obtain ⟨head, hhd, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines htmaj hhd
    simp only [arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨⟨dh, kh⟩⟩ := head
    simp only [ExprOps.node_kind] at hok
    simp only [absExpr_mk] at hhabs
    cases kh with
    | Const t2 ust =>
      obtain ⟨ht2, hust⟩ := CoreK.wf_const_inv hhwf rfl
      have hhead : ConLeche.Cached.ExprC.getAppFn (absExpr tmaj)
          = ConLeche.Expr.const (absName t2) (absLevels ust) := by
        rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]; simp [absExprKind]
      obtain ⟨targs, hta, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨htaabs, htawf⟩ := ExprOps.get_app_args_refines htmaj hta
      have hargs : ConLeche.Cached.ExprC.getAppArgs (absExpr tmaj) = absExprs targs := by
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← htaabs]
      obtain ⟨bq, hbq, hok⟩ := bind_eq_ok_iff.mp hok
      have hbqv := Name.beq_refines ht2 ht hbq
      try simp only [arc_deref_eq, bind_tc_ok] at hok
      have hlenl : (absConstantVal cvt).levelParams.length = cvt.level_params.val.length := by
        simp [absConstantVal, absNames]
      have hlenu : (absLevels ust).length = ust.val.length := by simp [absLevels]
      have hlena : (absExprs targs).length = targs.val.length := by simp [absExprs]
      have hepE : (absIndCaps caps).etaParams = caps.eta_params.val := rfl
      cases bq with
      | false =>
        have hne : ¬ (absName t2 = absName t) := by
          intro h; rw [h] at hbqv; simp at hbqv
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorEtaClause]
        rw [run_bind2 hrun1, hhead]
        simp only [pure_bind, beq_iff_eq, hne, false_and, if_false]
        simp
      | true =>
        have heq : absName t2 = absName t := by
          have h' : decide (absName t2 = absName t) = true := hbqv.symm
          simpa using h'
        obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
        have hi1v : i1.val = targs.val.length := by
          simp only [lift_eq, Result.ok.injEq] at hi1
          rw [← hi1, ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        by_cases hnp : i1 = caps.eta_params
        case neg =>
          rw [if_pos (bne_iff_ne.mpr hnp)] at hok
          have hnp' : ¬ ((absExprs targs).length = (absIndCaps caps).etaParams) := by
            rw [hlena, ← hi1v, hepE]; intro hc; exact hnp (by scalar_tac)
          obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
          rw [Expr.dup_eq hcd] at hok
          simp only [Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
          simp only [majorToCtorEtaClause]
          rw [run_bind2 hrun1, hhead]
          simp only [pure_bind]
          rw [hargs, if_neg (fun hc => hnp' hc.2.1)]
          simp
        case pos =>
          have hcond1 : ¬ ((i1 != caps.eta_params) = true) := by
            simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hnp
          rw [if_neg hcond1] at hok
          have hnpE : (absExprs targs).length = (absIndCaps caps).etaParams := by
            rw [hlena, ← hi1v, hepE]; scalar_tac
          by_cases hlen : alloc.vec.Vec.len ust = alloc.vec.Vec.len cvt.level_params
          case neg =>
            rw [if_pos (bne_iff_ne.mpr hlen)] at hok
            have hlen' : ¬ ((absLevels ust).length
                = (absConstantVal cvt).levelParams.length) := by
              rw [hlenl, hlenu]
              have h1 := alloc.vec.Vec.len_val cvt.level_params
              have h2 := alloc.vec.Vec.len_val ust
              intro hc; exact hlen (by scalar_tac)
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
            simp only [majorToCtorEtaClause]
            rw [run_bind2 hrun1, hhead]
            simp only [pure_bind]
            rw [hargs, if_neg (fun hc => hlen' hc.2.2.1)]
            simp
          case pos =>
            have hcond2 : ¬ ((alloc.vec.Vec.len ust
                != alloc.vec.Vec.len cvt.level_params) = true) := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hlen
            rw [if_neg hcond2] at hok
            have hlenE : (absLevels ust).length
                = (absConstantVal cvt).levelParams.length := by
              rw [hlenl, hlenu]
              have h1 := alloc.vec.Vec.len_val cvt.level_params
              have h2 := alloc.vec.Vec.len_val ust
              scalar_tac
            obtain ⟨bz, hbz, hok⟩ := bind_eq_ok_iff.mp hok
            have hbzv : bz = ConLeche.capsNeverZero (absConstantVal cvt).levelParams
                (absLevels ust) (absIndCaps caps) :=
              CoreK.caps_never_zero_refines hcvt.2.1 hust hcaps hbz
            cases bz with
            | false =>
              obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
              rw [Expr.dup_eq hcd] at hok
              simp only [Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
              simp only [majorToCtorEtaClause]
              rw [run_bind2 hrun1, hhead]
              simp only [pure_bind]
              rw [hargs, if_neg (fun hc => by
                have h2 := hc.2.2.2
                rw [← hbzv] at h2
                simp at h2)]
              simp
            | true =>
              have hnz : ConLeche.capsNeverZero (absConstantVal cvt).levelParams
                  (absLevels ust) (absIndCaps caps) = true := hbzv.symm
              have hc1 : ((absName t2 == absName t) = true ∧
                  (absExprs targs).length = (absIndCaps caps).etaParams ∧
                  (absLevels ust).length = (absConstantVal cvt).levelParams.length ∧
                  ConLeche.capsNeverZero (absConstantVal cvt).levelParams (absLevels ust)
                    (absIndCaps caps) = true) :=
                ⟨by rw [heq]; simp, hnpE, hlenE, hnz⟩
              obtain ⟨projs, hpj, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨hpjrun, hpjwf⟩ := hd.projApps hfe hfrel ht hust htawf hmajor hpj
              have hpjL : ∀ lz, (ConLeche.Cached.projAppsI lfe (absName t) (absName t)
                  (absLevels ust) (absExprs targs) (absExpr major)
                  (absIndCaps caps).etaFields).run lz = .ok (absExprs projs, lz) := hpjrun
              obtain ⟨tc, htc, hok⟩ := bind_eq_ok_iff.mp hok
              have htcv : tc = targs := Env.exprs_copy_refines htc
              obtain ⟨spine, hsp, hok⟩ := bind_eq_ok_iff.mp hok
              rw [htcv] at hsp
              obtain ⟨hspabs, hspwf⟩ := CoreK.append_exprs_refines htawf hpjwf hsp
              obtain ⟨nn, hnn, hok⟩ := bind_eq_ok_iff.mp hok
              rw [name_dup_eq] at hnn
              have hnnv : nn = caps.eta_ctor := (Result.ok_injective hnn).symm
              subst hnnv
              obtain ⟨v2, hv2, hok⟩ := bind_eq_ok_iff.mp hok
              have hv2v : v2 = ust := Env.levels_copy_refines hv2
              subst hv2v
              obtain ⟨hh, hhc, hok⟩ := bind_eq_ok_iff.mp hok
              have hhabs2 : absExpr hh
                  = ConLeche.Expr.const (absName caps.eta_ctor) (absLevels v2) :=
                Expr.mk_const_refines hhc
              have hhwf2 : ExprWF hh := Expr.mk_const_wf hcaps.1 hust hhc
              obtain ⟨fab, hfb, hok⟩ := bind_eq_ok_iff.mp hok
              rw [StateC.mk_app_n_m_eq] at hfb
              obtain ⟨hfabs, hfabwf⟩ := ExprOpsC.mk_app_n_refines hhwf2 hspwf hfb
              rw [hhabs2, hspabs] at hfabs
              have hfabL : ConLeche.Cached.ExprC.mkAppN
                  (ConLeche.Expr.const (absIndCaps caps).etaCtor (absLevels v2))
                  (absExprs targs ++ absExprs projs) = absExpr fab := hfabs.symm
              obtain ⟨b2, hb2, hok⟩ := bind_eq_ok_iff.mp hok
              have hb2v := hd.fabScopeOk hfabwf hmajor hb2
              cases b2 with
              | false =>
                obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                rw [Expr.dup_eq hcd] at hok
                simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                obtain ⟨rfl, rfl⟩ := hok
                refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
                simp only [majorToCtorEtaClause]
                rw [run_bind2 hrun1, hhead]
                simp only [pure_bind]
                rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                simp only [ConLeche.Cached.mkAppNM, pure_bind]
                rw [hfabL, ← hb2v]
                simp
              | true =>
                -- `const_ty_at_m` is read *outside* the `certs` gate, exactly where
                -- `ConLeche/Cached/CoreC.lean:619` has `constTyAtM` (task #61), so
                -- both modes move the memo table the same way.
                obtain ⟨⟨rcty, st2⟩, hcty, hok⟩ := bind_eq_ok_iff.mp hok
                cases rcty with
                | Err e =>
                  simp at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine Out.err ?_
                  simp only [majorToCtorEtaClause]
                  rw [run_bind2 hrun1, hhead]
                  simp only [pure_bind]
                  rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                  simp only [ConLeche.Cached.mkAppNM, pure_bind]
                  rw [hfabL, ← hb2v]
                  simp only [if_true]
                  exact ErrSim.bindCM (StateC.const_ty_at_m_err hwf1 hfe hrl.1 hust hcty
                    lst1 lfe hrel1 hfrel (absIndCaps caps).etaCtor)
                | Ok cty =>
                  obtain ⟨lstc, hrunc, hrelc, hwfc, hctywf⟩ :=
                    StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf1 hfe
                      hrl.1 hust hcty lst1 lfe hrel1 hfrel (absIndCaps caps).etaCtor
                  have hruncL : (ConLeche.Cached.constTyAtM lfe (absIndCaps caps).etaCtor
                      (absRecRule rl).ctor (absLevels v2)).run lst1
                      = .ok (absExpr cty, lstc) := hrunc
                  try dsimp only at hok
                  obtain ⟨p, hp, hok⟩ := bind_eq_ok_iff.mp hok
                  obtain ⟨b3, hb3, hp⟩ := bind_eq_ok_iff.mp hp
                  have hb3v := Env.certs_refines hb3
                  cases b3 with
                  | false =>
                    rw [← Result.ok_injective hp] at hok
                    try dsimp only at hok
                    cases oc with
                    | Ok r =>
                      obtain ⟨lste, hrune, hrele, hwfe, hrwf⟩ :=
                        (eta_rescue_certs_i_refines hd d caps hfabwf hmajor htmaj).apply
                          hwfc hfe hok hrelc hfrel
                      refine ⟨lste, ?_, hrele, hwfe, hrwf⟩
                      simp only [majorToCtorEtaClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb2v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                      simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                      exact hrune
                    | Err e =>
                      refine Out.err ?_
                      simp only [majorToCtorEtaClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb2v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                      simp only [Bool.false_eq_true, if_false, pure_bind, if_true]
                      exact (eta_rescue_certs_i_refines hd d caps hfabwf hmajor
                        htmaj).apply_err hwfc hfe hok hrelc hfrel
                  | true =>
                    try dsimp only at hp
                    obtain ⟨⟨rcert, st4⟩, hic, hp⟩ := bind_eq_ok_iff.mp hp
                    rw [← Result.ok_injective hp] at hok
                    try dsimp only at hok
                    cases rcert with
                    | Err e =>
                      simp at hok
                      obtain ⟨rfl, rfl⟩ := hok
                      have hicerr := (hd.iotaCerts d false hctywf hspwf).apply_err
                        hwfc hfe hic hrelc hfrel
                      rw [hspabs] at hicerr
                      refine Out.err ?_
                      simp only [majorToCtorEtaClause]
                      rw [run_bind2 hrun1, hhead]
                      simp only [pure_bind]
                      rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                      simp only [ConLeche.Cached.mkAppNM, pure_bind]
                      rw [hfabL, ← hb2v]
                      simp only [if_true]
                      rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                      simp only [reduceIte]
                      exact ErrSim.bindCM hicerr
                    | Ok b4 =>
                      obtain ⟨lsti, hruni, hreli, hwfi, -⟩ :=
                        (hd.iotaCerts d false hctywf hspwf).apply hwfc hfe hic hrelc hfrel
                      rw [hspabs] at hruni
                      cases b4 with
                      | false =>
                        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                        rw [Expr.dup_eq hcd] at hok
                        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                        obtain ⟨rfl, rfl⟩ := hok
                        refine ⟨lsti, ?_, hreli, hwfi, hmajor⟩
                        simp only [majorToCtorEtaClause]
                        rw [run_bind2 hrun1, hhead]
                        simp only [pure_bind]
                        rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                        simp only [ConLeche.Cached.mkAppNM, pure_bind]
                        rw [hfabL, ← hb2v]
                        simp only [if_true]
                        rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                        simp only [reduceIte]
                        rw [run_bind hruni]
                        simp
                      | true =>
                        cases oc with
                        | Ok r =>
                          obtain ⟨lste, hrune, hrele, hwfe, hrwf⟩ :=
                            (eta_rescue_certs_i_refines hd d caps hfabwf hmajor htmaj).apply
                              hwfi hfe hok hreli hfrel
                          refine ⟨lste, ?_, hrele, hwfe, hrwf⟩
                          simp only [majorToCtorEtaClause]
                          rw [run_bind2 hrun1, hhead]
                          simp only [pure_bind]
                          rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                          simp only [ConLeche.Cached.mkAppNM, pure_bind]
                          rw [hfabL, ← hb2v]
                          simp only [if_true]
                          rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                          simp only [reduceIte]
                          rw [run_bind hruni]
                          simp only [id_eq, if_true]
                          exact hrune
                        | Err e =>
                          refine Out.err ?_
                          simp only [majorToCtorEtaClause]
                          rw [run_bind2 hrun1, hhead]
                          simp only [pure_bind]
                          rw [hargs, if_pos hc1, run_bind (hpjL lst1)]
                          simp only [ConLeche.Cached.mkAppNM, pure_bind]
                          rw [hfabL, ← hb2v]
                          simp only [if_true]
                          rw [run_bind hruncL, ConLeche.Cached.certAtI, ← hb3v]
                          simp only [reduceIte]
                          rw [run_bind hruni]
                          simp only [id_eq, if_true]
                          exact (eta_rescue_certs_i_refines hd d caps hfabwf hmajor
                            htmaj).apply_err hwfi hfe hok hreli hfrel
    | _ =>
      all_goals (
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, hmajor⟩
        simp only [majorToCtorEtaClause]
        rw [run_bind2 hrun1, ConLeche.Cached.ExprC.getAppFn_spec, ← hhabs]
        simp [absExprKind])

set_option maxRecDepth 8000 in
/-- `ConLeche/Cached/CoreC.lean:544` — **`major_to_ctor_i` refines
`majorToCtorI`** (`core_c.rs:1298`): the cheap syntactic dispatch — already a
constructor application, a *single* recursor rule whose constructor is stored
and whose type's `piResult` is headed by a stored inductive — and then the
three rescue clauses, one per install-time bit.  The cited `_recName` is unused
in the Lean too, so the port drops it and the lemma quantifies over it. -/
theorem major_to_ctor_i_refines (hw : Wrappers mode fuel) (hd : MajorDeps mode fuel)
    (d : Std.U64) (recName : ConLeche.Name) {rules : alloc.vec.Vec env.RecRule}
    {major : expr.Expr} (hrules : RecRulesWF rules) (hmajor : ExprWF major) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.major_to_ctor_i mode fuel st fe d rules major)
      (fun lfe => ConLeche.Cached.majorToCtorI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val recName (absRecRules rules) (absExpr major)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  simp only []
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfrel hfe
  have hfw : FindWF fe := FindWF.of_wf hfe
  unfold cached.core_c.major_to_ctor_i at hok
  obtain ⟨bc, hbc, hok⟩ := bind_eq_ok_iff.mp hok
  have hbcv : bc = ConLeche.Cached.isCtorAppC lfe (absExpr major) := by
    rw [ConLeche.Cached.isCtorAppC, ConLeche.Cached.ExprC.getAppFn_spec]
    exact CoreK.is_ctor_app_refines hfa hmajor hbc
  cases bc with
  | true =>
    obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
    rw [Expr.dup_eq hcd] at hok
    simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact ⟨lst, by rw [majorToCtorI_stuck_ctorApp _ _ _ _ _ hbcv.symm]; simp,
      hrel, hwf, hmajor⟩
  | false =>
    have hctor : ConLeche.Cached.isCtorAppC lfe (absExpr major) = false := hbcv.symm
    have hvlen : (alloc.vec.Vec.len rules).val = rules.val.length :=
      alloc.vec.Vec.len_val rules
    by_cases hn1 : alloc.vec.Vec.len rules = 1#usize
    case neg =>
      rw [if_pos (bne_iff_ne.mpr hn1)] at hok
      obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hcd] at hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      have hlen : (absRecRules rules).length ≠ 1 := by
        simp only [absRecRules, List.length_map]
        intro hc
        exact hn1 (Std.UScalar.eq_of_val_eq (by rw [hvlen, hc]; simp))
      exact ⟨lst, by rw [majorToCtorI_stuck_rules _ _ _ _ _ hctor hlen]; simp,
        hrel, hwf, hmajor⟩
    case pos =>
      have hcond : ¬ ((alloc.vec.Vec.len rules != 1#usize) = true) := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact hn1
      rw [if_neg hcond] at hok
      obtain ⟨rl, hidx, hok⟩ := bind_eq_ok_iff.mp hok
      have hlen1 : rules.val.length = 1 := by
        rw [← hvlen, hn1]; simp
      have hg : rules.val[0]? = some rl := ExprOps.vec_index_getElem? hidx
      have hvl : rules.val = [rl] := by
        rcases hl : rules.val with _ | ⟨x, xs⟩
        · rw [hl] at hlen1; simp at hlen1
        · rw [hl] at hlen1 hg
          simp only [List.length_cons] at hlen1
          have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hxs
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
          rw [hg]
      have hrlwf : RecRuleWF rl := hrules rl (by rw [hvl]; simp)
      have hrulesL : absRecRules rules = [absRecRule rl] := by
        simp only [absRecRules, hvl, List.map_cons, List.map_nil]
      obtain ⟨o, hprobe, hok⟩ := bind_eq_ok_iff.mp hok
      cases o with
      | none =>
        obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hcd] at hok
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        have hmiss := CoreK.ctor_probe_miss CoreK.envFacts hfa hfw hrlwf.1 hprobe
        refine ⟨lst, ?_, hrel, hwf, hmajor⟩
        rw [hrulesL, majorToCtorI_stuck_ctor _ _ _ _ _ hctor hmiss]; simp
      | some tr =>
        obtain ⟨cvj, cn_p, cn_f⟩ := tr
        obtain ⟨hhit, hcvjwf⟩ := CoreK.ctor_probe_hit CoreK.envFacts hfa hfw hrlwf.1 hprobe
        obtain ⟨res, hres, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hresabs, hreswf⟩ := ExprOps.pi_result_refines hcvjwf.2.2 hres
        obtain ⟨head, hhd, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines hreswf hhd
        rw [hresabs] at hhabs
        simp only [arc_deref_eq, bind_tc_ok] at hok
        obtain ⟨⟨dh, kh⟩⟩ := head
        simp only [ExprOps.node_kind] at hok
        simp only [absExpr_mk] at hhabs
        cases kh with
        | Const t1 us =>
          obtain ⟨ht1, hus⟩ := CoreK.wf_const_inv hhwf rfl
          have hhead : ((absConstantVal cvj).type.piResult).getAppFn
              = ConLeche.Expr.const (absName t1) (absLevels us) := by
            show ((absExpr cvj.ty).piResult).getAppFn = _
            rw [← hhabs]; simp [absExprKind]
          obtain ⟨o1, hind, hok⟩ := bind_eq_ok_iff.mp hok
          cases o1 with
          | none =>
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            have hmiss := CoreK.ind_probe_miss CoreK.envFacts hfa hfw ht1 hind
            refine ⟨lst, ?_, hrel, hwf, hmajor⟩
            rw [hrulesL, majorToCtorI_stuck_ind _ _ _ _ _ hctor hhit hhead hmiss]; simp
          | some pr =>
            obtain ⟨cvt, caps⟩ := pr
            try dsimp only at hok
            try simp only [] at hok
            obtain ⟨hihit, hcvtwf, hcapswf⟩ :=
              CoreK.ind_probe_hit CoreK.envFacts hfa hfw ht1 hind
            cases hkb : rl.k with
            | true =>
              have hk : rl.k = true := hkb
              rw [hkb] at hok
              have hok' : cached.core_c.major_to_ctor_k_i mode fuel st fe d rl cvj cn_p t1
                  major = ok (oc, st') := hok
              cases oc with
              | Ok r =>
                obtain ⟨lstk, hrunk, hrelk, hwfk, hrwf⟩ :=
                  (major_to_ctor_k_i_refines hw hd d cn_p hrlwf hcvjwf ht1 hmajor).apply
                    hwf hfe hok' hrel hfrel
                refine ⟨lstk, ?_, hrelk, hwfk, hrwf⟩
                rw [hrulesL, majorToCtorI_eq_k _ _ _ _ _ hctor rfl hhit hhead hihit hk]
                exact hrunk
              | Err e =>
                refine Out.err ?_
                rw [hrulesL, majorToCtorI_eq_k _ _ _ _ _ hctor rfl hhit hhead hihit hk]
                exact (major_to_ctor_k_i_refines hw hd d cn_p hrlwf hcvjwf ht1
                  hmajor).apply_err hwf hfe hok' hrel hfrel
            | false =>
              rw [hkb] at hok
              have hk' : (absRecRule rl).k = false := hkb
              cases heb : rl.eta with
              | true =>
                have he : rl.eta = true := heb
                rw [heb] at hok
                have hok' : cached.core_c.major_to_ctor_eta_i mode fuel st fe d rl cvt caps
                    t1 major = ok (oc, st') := hok
                cases oc with
                | Ok r =>
                  obtain ⟨lste, hrune, hrele, hwfe, hrwf⟩ :=
                    (major_to_ctor_eta_i_refines hd d hrlwf hcvtwf hcapswf ht1 hmajor).apply
                      hwf hfe hok' hrel hfrel
                  refine ⟨lste, ?_, hrele, hwfe, hrwf⟩
                  rw [hrulesL,
                    majorToCtorI_eq_eta _ _ _ _ _ hctor rfl hhit hhead hihit hk' he]
                  exact hrune
                | Err e =>
                  refine Out.err ?_
                  rw [hrulesL,
                    majorToCtorI_eq_eta _ _ _ _ _ hctor rfl hhit hhead hihit hk' he]
                  exact (major_to_ctor_eta_i_refines hd d hrlwf hcvtwf hcapswf ht1
                    hmajor).apply_err hwf hfe hok' hrel hfrel
              | false =>
                rw [heb] at hok
                have he' : (absRecRule rl).eta = false := heb
                obtain ⟨an, han, hok⟩ := bind_eq_ok_iff.mp hok
                obtain ⟨hanabs, hanwf⟩ := CoreK.pinned_and_name an han
                obtain ⟨ba, hba, hok⟩ := bind_eq_ok_iff.mp hok
                have hbav := Name.beq_refines ht1 hanwf hba
                rw [hanabs] at hbav
                cases ba with
                | true =>
                  have hand : absName t1 = ConLeche.andName := by
                    have h' : decide (absName t1 = ConLeche.andName) = true := hbav.symm
                    simpa using h'
                  cases oc with
                  | Ok r =>
                    obtain ⟨lsta, hruna, hrela, hwfa, hrwf⟩ :=
                      (major_to_ctor_and_i_refines hw hd d cn_p hrlwf hcvjwf ht1
                        hmajor).apply hwf hfe hok hrel hfrel
                    refine ⟨lsta, ?_, hrela, hwfa, hrwf⟩
                    rw [hrulesL,
                      majorToCtorI_eq_and _ _ _ _ _ hctor rfl hhit hhead hihit hk' he' hand]
                    exact hruna
                  | Err e =>
                    refine Out.err ?_
                    rw [hrulesL,
                      majorToCtorI_eq_and _ _ _ _ _ hctor rfl hhit hhead hihit hk' he' hand]
                    exact (major_to_ctor_and_i_refines hw hd d cn_p hrlwf hcvjwf ht1
                      hmajor).apply_err hwf hfe hok hrel hfrel
                | false =>
                  have hand : absName t1 ≠ ConLeche.andName := by
                    intro h; rw [h] at hbav; simp at hbav
                  obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
                  rw [Expr.dup_eq hcd] at hok
                  simp only [Result.ok.injEq, Prod.mk.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst, ?_, hrel, hwf, hmajor⟩
                  rw [hrulesL, majorToCtorI_stuck_bits _ _ _ _ _ hctor hhit hhead hihit
                    hk' he' hand]
                  simp
        | _ =>
          all_goals (
            obtain ⟨c, hcd, hok⟩ := bind_eq_ok_iff.mp hok
            rw [Expr.dup_eq hcd] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst, ?_, hrel, hwf, hmajor⟩
            rw [hrulesL, majorToCtorI_stuck_head _ _ _ _ _ hctor hhit
              (by
                show ∀ T us, ((absExpr cvj.ty).piResult).getAppFn ≠ ConLeche.Expr.const T us
                rw [← hhabs]; simp [absExprKind])]
            simp)

end Arms

/-! ## The census

Every statement in this file is unconditional in the mode: since task #61 put
`const_ty_at_m` back outside the `certs` gate, the three rescue arms hold at
`.trusted` as well as at `.verified`, and nothing here depends on `sorryAx`. -/

/-- info: 'ConRon.Refine.Core.lit_major_to_ctor_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lit_major_to_ctor_i_refines

/-- info: 'ConRon.Refine.Core.proj_lit_to_ctor_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proj_lit_to_ctor_i_refines

/-- info: 'ConRon.Refine.Core.k_type_and_irrel_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms k_type_and_irrel_i_refines

/-- info: 'ConRon.Refine.Core.eta_rescue_certs_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eta_rescue_certs_i_refines

/-- info: 'ConRon.Refine.Core.major_to_ctor_k_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms major_to_ctor_k_i_refines

/-- info: 'ConRon.Refine.Core.major_to_ctor_eta_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms major_to_ctor_eta_i_refines

/-- info: 'ConRon.Refine.Core.major_to_ctor_and_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms major_to_ctor_and_i_refines

/-- info: 'ConRon.Refine.Core.major_to_ctor_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms major_to_ctor_i_refines

end ConRon.Refine.Core

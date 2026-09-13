/-
# `Arms/InferSpineIO.lean` — the io-grade application-inference spine
(task #55, `CORE_PLAN.md` step 6)

Two helpers of `crates/con-ron-core/src/cached/core_c.rs`, the io twin of the
`infer_spine_i` cluster:

* `infer_spine_io_i` (`core_c.rs:2761`) — con-leche's `inferSpineIOI`
  (`ConLeche/Cached/CoreC.lean:1069`), the gated telescope walk;
* `infer_spine_io_cert_i` (`core_c.rs:2853`) — the per-argument certificate
  the walk runs when the gate does *not* fire, which con-leche writes inline
  in `inferSpineIOI`'s two `unless` blocks.

Three things cost thought.

1. **The suffix correspondence.**  con-leche recurses on the argument *list*;
   the Rust walks `args : Vec Expr` by an index `i : Usize`.  The
   correspondence is `(absExprs args).drop i.val`, and the induction is on
   `args.val.length - i.val` (`Refine/CoreKVec.lean` owns the same shape for
   the `core_k` index recursions).

2. **The accumulator's orientation.**  The deferred substitution is consumed
   by `state_c::inst_list_rev_m`, which *is* `expr_ops_c::instantiate_rev`
   (`Refine/StateC.lean`'s `inst_list_rev_m_eq`) and refines
   `ExprC.instantiateRev` — the substitution on the **reversed** accumulator
   (`Refine/ExprOpsCSubst.lean`'s `instantiate_rev_refines` states it as
   `Expr.instantiateList … (absExprs vs).reverse`, and con-leche's
   `instantiateRev_spec` reads the cited definition the same way).  So the
   accumulator itself is *not* reversed: the Rust `Vec` and con-leche's
   `Array` carry the arguments in spine order, oldest first, and the reversal
   happens inside the substitution.  con-leche's accumulator is an
   `Array ExprC`, so the abstraction is `(absExprs acc).toArray`; a `push` on
   either side is `++ [a]` on the underlying list.

3. **The gate is mode-parametric.**  `env::io_skip mode mt.pw` refines
   `CheckMode.ioSkip` (`Refine/Env.lean`'s `io_skip_refines`) at *both*
   modes, so neither lemma below ever looks inside `mode`: the licence is
   read, not evaluated.  The syntactic `.ForallE` arm and the whnf'd arm each
   split on the returned `Bool`, exactly as the Rust's two tail calls do
   (task #18's rule: a gated certificate whose arms rejoin must be two tail
   calls).

The `.M`-suffixed `Array Std.U32` constants (`infer_spine_io_i.M_FN`,
`infer_spine_io_cert_i.M_MISMATCH`) are error-message code points reached
only on the `.Err` path, and nothing is claimed on failure (DESIGN.md §3.5),
so they carry no theorem.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKGuards
import ConRon.Refine.ExprOpsCSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! `attribute [local simp]` does not travel across files, so `Shape.lean`'s
monad-plumbing set (`CheckCM = StateT CState (Except CheckError)`) is
re-declared here verbatim. -/
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure


/-! ## Two pieces of `Result` plumbing

`Abs.lean`'s `bind_eq_ok_iff` is stated for `Bind.bind`; unfolding the class
projection — which the simp set above does, for the con-leche side — turns
the port's binds into `Aeneas.Std.bind`, where it no longer fires.  The first
lemma restores it.  The second is the `let (r, st) ← f` shape every
state-threading call in `cached::core_c` has: `bind_eq_ok_iff` leaves a
pattern-`let` that neither `simp` nor `split` sees through, so the
destructuring is done once here, where the conclusion is stated in reduced
form. -/

@[local simp] private theorem std_bind_eq_ok_iff {α β : Type} {e : Result α}
    {f : α → Result β} {v : β} :
    (Aeneas.Std.bind e f = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v :=
  bind_eq_ok_iff

private theorem ite_eq_ok {c : Prop} [Decidable c] {α : Type} {x y : Result α}
    {v : α} (h : (if c then x else y) = ok v) :
    (c ∧ x = ok v) ∨ (¬ c ∧ y = ok v) := by
  by_cases hc : c
  · exact Or.inl ⟨hc, by rwa [if_pos hc] at h⟩
  · exact Or.inr ⟨hc, by rwa [if_neg hc] at h⟩

private theorem bindP_eq_ok {α β γ : Type} {e : Result (α × β)}
    {f : α → β → Result γ} {v : γ}
    (h : (do let (x, y) ← e; f x y) = ok v) :
    ∃ x y, e = ok (x, y) ∧ f x y = ok v := by
  obtain ⟨⟨x, y⟩, h1, h2⟩ := bind_eq_ok_iff.mp h
  exact ⟨x, y, h1, h2⟩

/-! ## The io view's slots

`CoreFnsI.ioView` is `{ r with infer := r.inferIO }`, so the only slot the
view changes is `infer`.  These three keep the view *folded* (the recursive
call's statement mentions `ioView`) while letting a `whnf`/`defeq`/`inferIO`
call site see the plain slot. -/

@[local simp] private theorem ioView_whnf (r : ConLeche.Cached.CoreFnsI) :
    r.ioView.whnf = r.whnf := rfl

@[local simp] private theorem ioView_defeq (r : ConLeche.Cached.CoreFnsI) :
    r.ioView.defeq = r.defeq := rfl

@[local simp] private theorem ioView_infer (r : ConLeche.Cached.CoreFnsI) :
    r.ioView.infer = r.inferIO := rfl

/-! ## The two local facts about the parts -/

/-- `ConLeche/Cached/StateC.lean:201-205` — **the `inst_list_rev_m` step**:
the port's `state_c::inst_list_rev_m e vs 0` is con-leche's
`instListRevM e vs`, a `pure` on both sides (con-leche says explicitly that
it is deliberately not memoised), so this is a plain value equation and not a
`Sim`. -/
private theorem inst_list_rev_m_val {e r : expr.Expr}
    {vs : alloc.vec.Vec expr.Expr} (he : ExprWF e) (hvs : ExprsWF vs)
    (h : cached.state_c.inst_list_rev_m e vs 0#u64 = ok r) :
    absExpr r = ConLeche.Cached.ExprC.instantiateRev (absExpr e)
        (absExprs vs).toArray 0 ∧ ExprWF r := by
  rw [StateC.inst_list_rev_m_eq] at h
  obtain ⟨habs, hwf⟩ := ExprOpsC.instantiate_rev_refines he hvs h
  refine ⟨?_, hwf⟩
  rw [habs, ConLeche.Cached.ExprC.instantiateRev_spec]
  simp

/-- A well-formed `ForallE` node has well-formed parts — the `ForallE` twin of
`Refine/CoreKGuards.lean`'s `wf_app_inv`, which that file does not need. -/
private theorem wf_forall_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty b : expr.Expr} {m : expr.BinderMeta}
    (hk : e = .mk (.mk d (.ForallE ty b m))) : ExprWF ty ∧ ExprWF b := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ _ h1 => obtain ⟨d1, b1, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b1, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo m1 _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty1 bo m1 _ hty hbo _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.ForallE.injEq] at hk
    obtain ⟨-, rfl, rfl, -⟩ := hk
    exact ⟨hty, hbo⟩
  | @let_e ty1 v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- The certificate, **taken apart**: on success the io inference and the
`defeq` each ran, in order, and the second returned `true`.  This is the form
the spine walk needs — `inferSpineIOI` inlines the certificate into the two
arms of its `unless`, so the composed run of `infer_spine_io_cert_i_refines`
does not match there syntactically, while these two component runs do.  The
certificate's own `Sim` is read off it immediately below, so nothing is
proved twice. -/
private theorem cert_parts (hw : Wrappers mode fuel) (d : Std.U64)
    {a dom : expr.Expr} (ha : ExprWF a) (hdom : ExprWF dom)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    {st st' : cached.state_c.CState} (hwf : StateWF st)
    (hcert : cached.core_c.infer_spine_io_cert_i mode fuel st fe d a dom
      = ok (.Ok (), st'))
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) :
    ∃ ta lst1 lst2,
      (knot mode lfe fuel.val).inferIO d.val (absExpr a) lst = .ok (ta, lst1)
        ∧ (knot mode lfe fuel.val).defeq d.val ta (absExpr dom) lst1 = .ok (true, lst2)
        ∧ StateRel st' lst2 ∧ StateWF st' := by
  unfold cached.core_c.infer_spine_io_cert_i at hcert
  obtain ⟨r0, st1, h1, hcert⟩ := bindP_eq_ok hcert
  cases r0 with
  | Err err => simp at hcert
  | Ok ta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htaWF⟩ :=
      (hw.inferIOSim d ha).apply hwf hfe h1 hrel hfrel
    obtain ⟨r1, st2, h2, hcert⟩ := bindP_eq_ok hcert
    cases r1 with
    | Err err => simp at hcert
    | Ok b =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
        (hw.defeqSim d htaWF hdom).apply hwf1 hfe h2 hrel1 hfrel
      cases b with
      | false => simp at hcert
      | true =>
        simp at hcert
        subst hcert
        simp only [StateT.run] at hrun1 hrun2
        exact ⟨absExpr ta, lst1, lst2, hrun1, by simpa using hrun2, hrel2, hwf2⟩

/-- `ConLeche/Cached/CoreC.lean:1076-1079`, `:1087-1089` — **`infer_spine_io_cert_i`
refines the per-argument certificate** `let ta ← r.infer depth a; unless ←
r.defeq depth ta dom do throw (.invalid "application type mismatch")`
(`core_c.rs:2853`).  con-leche writes it inline in each of `inferSpineIOI`'s
two `unless mode.ioSkip …` blocks, so the Lean side here is that `do` block
and not a named definition; `r` is the record the knot ties the io body to,
whose `infer` slot is the io slot (`CoreFnsI.ioView`), which is why the port
calls `infer_io`.  The result is `()`, so the value abstraction is `id` and
nothing is claimed about it. -/
theorem infer_spine_io_cert_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {a dom : expr.Expr} (ha : ExprWF a) (hdom : ExprWF dom) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.infer_spine_io_cert_i mode fuel st fe d a dom)
      (fun lfe => do
        let ta ← (knot mode lfe fuel.val).inferIO d.val (absExpr a)
        unless (← (knot mode lfe fuel.val).defeq d.val ta (absExpr dom)) do
          throw (.invalid "application type mismatch")) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  obtain ⟨ta, lst1, lst2, hcI, hcD, hrel', hwf'⟩ :=
    cert_parts hw d ha hdom hfe hfrel hwf hok hrel
  exact ⟨lst2, by simp [hcI, hcD], hrel', hwf', trivial⟩

/-- The walk, by strong induction on the number of arguments still to
consume (`args.val.length - i.val`): every recursive call steps `i` up by one
and `args` never changes, which is the port's spelling of con-leche's
recursion on the tail of the argument list.  The three clauses of
`inferSpineIOI` are the three branches below — the empty suffix, the
syntactic `.forallE` step, and the normalizing step — and the gate splits
each of the last two in two, as the port's two tail calls do. -/
private theorem spine_aux (hw : Wrappers mode fuel) (N : Nat) :
    ∀ (d : Std.U64) (ty : expr.Expr) (acc args : alloc.vec.Vec expr.Expr)
      (i : Std.Usize), args.val.length - i.val = N →
      ExprWF ty → ExprsWF acc → ExprsWF args →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.infer_spine_io_i mode fuel st fe d ty acc args i)
        (fun lfe => ConLeche.Cached.inferSpineIOI (absMode mode)
          (knot mode lfe fuel.val).ioView lfe d.val (absExpr ty)
          (absExprs acc).toArray ((absExprs args).drop i.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro d ty acc args i hN hty hacc hargs fe lfe hfe hfrel st res st' hwf hok
      lst hrel
    unfold cached.core_c.infer_spine_io_i at hok
    rcases ite_eq_ok hok with ⟨hge, h⟩ | ⟨hge, h⟩ <;> clear hok
    · -- `i ≥ args.len`: the argument suffix is empty, and the walk is the
      -- deferred substitution `instListRevM ty acc`
      obtain ⟨e, hinst, h⟩ := bind_eq_ok_iff.mp h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨habs, hresWF⟩ := inst_list_rev_m_val hty hacc hinst
      have hlen := alloc.vec.Vec.len_val args
      have hdrop : List.drop i.val (absExprs args) = [] := by
        apply List.drop_eq_nil_of_le
        rw [absExprs, List.length_map]
        scalar_tac
      refine ⟨lst, ?_, hrel, hwf, hresWF⟩
      rw [hdrop, habs]
      simp [ConLeche.Cached.inferSpineIOI, ConLeche.Cached.instListRevM]
    · obtain ⟨⟨dt, kt⟩⟩ := ty
      cases kt
      case ForallE =>
        -- the syntactic `∀` step: no normalization, and the accumulator grows
        rename_i dm bd mtm
        obtain ⟨hdmWF, hbdWF⟩ := wf_forall_inv hty rfl
        simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
          expr.ExprNode.kind._simpLemma_, ConRon.Refine.State.expr_dup_eq] at h
        obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
        have hbv := Env.io_skip_refines hb
        rcases ite_eq_ok h with ⟨hbt, h⟩ | ⟨hbt, h⟩
        · -- the licence fires
          obtain ⟨a, hidx, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hlt, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
          obtain ⟨acc1, hpush, h⟩ := bind_eq_ok_iff.mp h
          have hacc1 := ExprOps.absExprs_push hpush
          have hacc1WF := ExprOps.exprsWF_push hacc haWF hpush
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          obtain ⟨lst2, hrun2, hrel2, hwf2, hresWF⟩ :=
            (ih (args.val.length - i2.val) (by omega) d bd acc1 args i2 rfl
              hbdWF hacc1WF hargs).apply hwf hfe h hrel hfrel
          refine ⟨lst2, ?_, hrel2, hwf2, hresWF⟩
          rw [hi2v, hacc1] at hrun2
          have hskip : (absMode mode).ioSkip (absPropWhen mtm.pw) = true := by
            rw [← hbv, hbt]
          simp only [StateT.run] at hrun2
          rw [hdrop]
          simp only [absExpr_mk, absExprKind, absBinderMeta]
          rw [ConLeche.Cached.inferSpineIOI.eq_def]
          simp [hskip, hrun2]
        · -- the licence does not fire: the certificate runs against the
          -- accumulator-substituted domain
          obtain ⟨dom2, hinstd, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨habsd, hdom2WF⟩ := inst_list_rev_m_val hdmWF hacc hinstd
          obtain ⟨a, hidx, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hlt, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
          obtain ⟨rc, st2, hcert, h⟩ := bindP_eq_ok h
          cases rc with
          | Err err => simp at h
          | Ok u =>
            obtain ⟨tav, lstA, lstB, hcI, hcD, hrel2, hwf2⟩ :=
              cert_parts hw d haWF hdom2WF hfe hfrel hwf hcert hrel
            obtain ⟨acc1, hpush, h⟩ := bind_eq_ok_iff.mp h
            have hacc1 := ExprOps.absExprs_push hpush
            have hacc1WF := ExprOps.exprsWF_push hacc haWF hpush
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
            obtain ⟨lst3, hrun3, hrel3, hwf3, hresWF⟩ :=
              (ih (args.val.length - i2.val) (by omega) d bd acc1 args i2 rfl
                hbdWF hacc1WF hargs).apply hwf2 hfe h hrel2 hfrel
            refine ⟨lst3, ?_, hrel3, hwf3, hresWF⟩
            rw [hi2v, hacc1] at hrun3
            have hskip : (absMode mode).ioSkip (absPropWhen mtm.pw) = false := by
              rw [← hbv]; simpa using hbt
            simp only [StateT.run] at hrun3
            rw [hdrop]
            simp only [absExpr_mk, absExprKind, absBinderMeta] at habsd ⊢
            rw [ConLeche.Cached.inferSpineIOI.eq_def]
            simp [ConLeche.Cached.instListRevM, ← habsd, hskip, hcI, hcD, hrun3]
      -- the nine remaining kinds are con-leche's one `| _ =>` clause, and the
      -- port's generated `match` repeats the same body in each, so one script
      -- discharges them all: substitute, normalize, and look for a `∀` again
      all_goals
        simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
          expr.ExprNode.kind._simpLemma_] at h
        obtain ⟨ty2, hinst, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨habs2, hty2⟩ := inst_list_rev_m_val hty hacc hinst
        obtain ⟨rw0, st1, hwn, h⟩ := bindP_eq_ok h
        cases rw0 with
        | Err err => simp at h
        | Ok w =>
          obtain ⟨lst1, hrun1, hrel1, hwf1, hwWF⟩ :=
            (hw.whnfSim d hty2).apply hwf hfe hwn hrel hfrel
          obtain ⟨⟨dw, kw⟩⟩ := w
          cases kw
          case ForallE =>
            -- the normalized head is a `∀`: the accumulator restarts at `#[a]`
            rename_i dm bd mtm
            obtain ⟨hdmWF, hbdWF⟩ := wf_forall_inv hwWF rfl
            simp only [expr.Expr._0._simpLemma_, expr.ExprNode.kind._simpLemma_,
              ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
            obtain ⟨pw1, hpw, h⟩ := bind_eq_ok_iff.mp h
            rw [PropWhen.dup_eq hpw] at h
            obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
            have hbv := Env.io_skip_refines hb
            rcases ite_eq_ok h with ⟨hbt, h⟩ | ⟨hbt, h⟩
            · -- the licence fires: no certificate, and the walk goes on
              obtain ⟨a, hidx, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hlt, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
              obtain ⟨acc2, hsing, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hacc2, hacc2WF⟩ := CoreK.expr_singleton_refines haWF hsing
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              obtain ⟨lst2, hrun2, hrel2, hwf2, hresWF⟩ :=
                (ih (args.val.length - i2.val) (by omega) d bd acc2 args i2 rfl
                  hbdWF hacc2WF hargs).apply hwf1 hfe h hrel1 hfrel
              refine ⟨lst2, ?_, hrel2, hwf2, hresWF⟩
              rw [hi2v, hacc2] at hrun2
              have hskip : (absMode mode).ioSkip (absPropWhen mtm.pw) = true := by
                rw [← hbv, hbt]
              simp only [StateT.run] at hrun1 hrun2
              rw [hdrop]
              simp only [absExpr_mk, absExprKind, absBinderMeta,
                absLiteral] at habs2 ⊢
              rw [ConLeche.Cached.inferSpineIOI.eq_def]
              simp [ConLeche.Cached.instListRevM, ← habs2, hrun1, hskip, hrun2]
            · -- the licence does not fire: the certificate runs, then the walk
              obtain ⟨a, hidx, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hlt, haWF, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
              obtain ⟨rc, st2, hcert, h⟩ := bindP_eq_ok h
              cases rc with
              | Err err => simp at h
              | Ok u =>
                obtain ⟨tav, lstA, lstB, hcI, hcD, hrel2, hwf2⟩ :=
                  cert_parts hw d haWF hdmWF hfe hfrel hwf1 hcert hrel1
                obtain ⟨acc2, hsing, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨hacc2, hacc2WF⟩ := CoreK.expr_singleton_refines haWF hsing
                obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
                obtain ⟨lst3, hrun3, hrel3, hwf3, hresWF⟩ :=
                  (ih (args.val.length - i2.val) (by omega) d bd acc2 args i2 rfl
                    hbdWF hacc2WF hargs).apply hwf2 hfe h hrel2 hfrel
                refine ⟨lst3, ?_, hrel3, hwf3, hresWF⟩
                rw [hi2v, hacc2] at hrun3
                have hskip : (absMode mode).ioSkip (absPropWhen mtm.pw) = false := by
                  rw [← hbv]; simpa using hbt
                simp only [StateT.run] at hrun1 hrun3
                rw [hdrop]
                simp only [absExpr_mk, absExprKind, absBinderMeta,
                  absLiteral] at habs2 ⊢
                rw [ConLeche.Cached.inferSpineIOI.eq_def]
                simp [ConLeche.Cached.instListRevM, ← habs2, hrun1, hskip, hcI,
                  hcD, hrun3]
          all_goals simp at h

/-- `ConLeche/Cached/CoreC.lean:1069` — **`infer_spine_io_i` refines
`inferSpineIOI`** (`core_c.rs:2761`): the io-grade telescope walk, at the
record the knot ties the io body to (`CoreFnsI.ioView`, task #18's
deviation 4 — the port's `infer_io`/`defeq`/`whnf` calls *are* that record's
`infer`/`defeq`/`whnf` slots).

The argument list is the suffix `args.val.drop i.val`, so the Lean side takes
`(absExprs args).drop i.val`; the accumulator is in spine order on both sides
(the reversal lives in `instantiateRev`), so it abstracts as
`(absExprs acc).toArray`.  `inferBodyIOI`'s call site is this lemma at
`acc = Vec::new()` and `i = 0`, which is con-leche's `#[]` and the whole
argument list. -/
theorem infer_spine_io_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {ty : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_spine_io_i mode fuel st fe d ty acc args i)
      (fun lfe => ConLeche.Cached.inferSpineIOI (absMode mode)
        (knot mode lfe fuel.val).ioView lfe d.val (absExpr ty)
        (absExprs acc).toArray ((absExprs args).drop i.val)) :=
  spine_aux hw _ d ty acc args i rfl hty hacc hargs

end

/-- info: 'ConRon.Refine.Core.infer_spine_io_cert_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_spine_io_cert_i_refines

/-- info: 'ConRon.Refine.Core.infer_spine_io_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_spine_io_i_refines

end ConRon.Refine.Core

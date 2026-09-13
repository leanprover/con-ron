/-
# The certificate group of the knot's arms (task #55)

`crates/con-ron-core/src/cached/core_c.rs`'s **certificates**: the helpers
`whnf_core` and `defeq` share, against `ConLeche/Cached/CoreC.lean`.

| group | port | con-leche |
|---|---|---|
| the fabricated projection spines | `proj_nodes_i`, `proj_apps_fn_i`, `proj_apps_i` | `projNodesI` `:369`, `projAppsFnI` `:359`, `projAppsI` `:381` |
| pairwise definitional equality | `def_eq_list_i(_from)` | `defEqListI` `:202` |
| the recursor-telescope certificate | `iota_certs_i(_aux)` | `iotaCertsI` `:197`, `iotaCertsIAux` `:168` |
| proof irrelevance | `proof_irrel_i`, `prop_legs_i` | `proofIrrelI` `:241` (and `propIrrelI` `:333`, whose `Prop` legs are the same block) |
| structure eta | `struct_eta_proj_certs_i(_from)`, `struct_eta_cert_with_i`, `struct_eta_cert_steps_i`, `struct_eta_cert_fields_i` | `structEtaProjCertsI` `:389`, `structEtaCertWithI` `:408` |

Four things cost thought.

1. **The three projection-spine builders are pure in the port** (`Vec<Expr>`,
   no `CState`) where con-leche writes them in `CheckCM` — `mkAppNM` is
   `pure (ExprC.mkAppN …)` (`Cached/StateC.lean:213`) and `towerSlotsAllF` is a
   pure index read.  Their shape is therefore `SimP` at
   `A := fun r => (pure (absExprs r) : CheckCM (List ExprC))`: the con-leche
   action *is* the `pure` of the port's list, which is exactly what a caller
   needs to rewrite the action away in a `do` block.  `projNodesI_pure` and
   `projAppsFnI_pure` are the two state-freeness facts, each an induction on
   the cited `List Nat` (always `List.range nF` at the call sites, whence the
   port's `j`/`n_f` counter).

2. **The index loops.**  `def_eq_list_i_from` walks two `Vec`s with one cursor
   where `defEqListI` recurses on two `List`s; the correspondence is the pair
   of suffixes `(absExprs xs).drop i`, `(absExprs ys).drop i`, and the
   induction is on `xs.val.length - i.val`.  `iota_certs_i_aux` is the cited
   `termination_by (args.length, acc.length)`: a strong induction on
   `args.val.length - i.val` with an inner one on `acc.val.length`, the inner
   step being the `bvar` arm, which empties the accumulator without consuming
   an argument.  `struct_eta_proj_certs_i_from` is the plain `n_f - j` loop.

3. **`prop_legs_i` has no con-leche function of its own**: it is the `Prop`
   leg block that `proofIrrelI` (`:252-268`) and `propIrrelI` (`:344-354`)
   spell out *verbatim*, hoisted in the port so that both twins call it.
   `propLegsI` below is that block, written out once; the identity against the
   cited definition is `rfl`, so nothing is assumed.

4. **The two `certAtI` gates of the structure-eta certificate.**  The cited
   body reads the type former's type *before* the first gate (`:437`), so
   `constTyAtM` moves the state — and can `throw` — at `.trusted` too; the
   port does the same since task #61, and `struct_eta_cert_steps_i_refines`
   therefore applies `StateC.const_ty_at_m_refines` **before** splitting on
   `env::certs`.  Each gate is discharged into one local record,
   `∀ f, (certAtI … >>= f).run lst = (f b).run lst'`, which is what a caller
   needs to step through the `do` block at either mode.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKProj
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.PropRead

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## Plumbing

`Shape.lean`'s `local simp` set does not travel through the import, so it is
re-declared here. -/

attribute [local simp] StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-! ## The two lower-tier ingredients this file does not own

Both are `Refine/StateC.lean`'s own open ends, named there and reached from
`iota_certs_i_aux`/`struct_eta_*`'s `inst_list_m` and `const_ty_at_m` calls.
Neither is a fact about *this* file's inputs: they are global facts about the
port's `cached::state_c`, so they travel as one hypothesis record, to be
discharged by the coordinator once task #51 lands and `InstCSize` is folded
into `State.lean`'s `StateRel` (`Refine/StateC.lean:48-58`, `:1883-1890`). -/

/-- The `cached::state_c` facts `Refine/StateC.lean` leaves open. -/
structure StateCOpen : Prop where
  /-- Task #51's `expr_ops_c::instantiate_list`, which
  `StateC.inst_list_m_refines` takes as an ingredient. -/
  instList : StateC.InstantiateListRefines
  /-- `StateRel`'s missing `instC` `len` clause: `Refine/StateC.lean` says in
  so many words that `InstCSize` is **to be unified into `StateRel`**, which is
  exactly this implication. -/
  instSize : ∀ st lst, StateRel st lst → StateC.InstCSize st lst

/-! ## `proj_nodes_i` — the tower spelling of a fabricated projection spine

`ConLeche/Cached/CoreC.lean:369-376 projNodesI` (`core_c.rs:717`). -/

/-- `projNodesI` touches no state: it is the `pure` of `List.map`. -/
theorem projNodesI_pure (T : ConLeche.Name) (b : ConLeche.Cached.ExprC) :
    ∀ l : List Nat, ConLeche.Cached.projNodesI T b l
      = pure (l.map (fun i => ConLeche.Expr.proj T i b)) := by
  intro l
  induction l with
  | nil => rfl
  | cons i l ih => rw [ConLeche.Cached.projNodesI, ih]; rfl

/-- The port's index loop: the entries from `j` on, appended to `out`. -/
theorem proj_nodes_i_abs (N : Nat) :
    ∀ (t : name.Name) (b : expr.Expr) (n_f j : Std.U64)
      (out r : alloc.vec.Vec expr.Expr), NameWF t → ExprWF b → ExprsWF out →
      n_f.val - j.val = N →
      cached.core_c.proj_nodes_i t b n_f j out = ok r →
      absExprs r = absExprs out ++ (List.range' j.val N).map
          (fun i => ConLeche.Expr.proj (absName t) i (absExpr b))
        ∧ ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t b n_f j out r ht hb hout hN h
    unfold cached.core_c.proj_nodes_i at h
    split at h
    · rename_i hge
      have : N = 0 := by scalar_tac
      subst this
      rw [← Result.ok_injective h]
      exact ⟨by simp, hout⟩
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      simp only [name_dup_eq, expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨e1, he1, out1, hpush, i1, hi1, hrec⟩ := h
      have hi1v : i1.val = j.val + 1 := HashMap.uscalar_add_eq hi1
      have hNpos : N = (n_f.val - i1.val) + 1 := by omega
      have hout1 : absExprs out1
          = absExprs out ++ [ConLeche.Expr.proj (absName t) j.val (absExpr b)] := by
        rw [absExprs, vec_push_val hpush]
        simp [absExprs, Expr.proj_refines he1]
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hpush] at hx
        rcases List.mem_append.1 hx with h1 | h1
        · exact hout x h1
        · rw [List.mem_singleton.1 h1]; exact Expr.proj_wf ht hb he1
      obtain ⟨habs, hwf⟩ := ih (n_f.val - i1.val) (by omega) t b n_f i1 out1 r
        ht hb hout1wf rfl hrec
      refine ⟨?_, hwf⟩
      rw [habs, hout1, hNpos, hi1v, List.range'_succ]
      simp

/-- `ConLeche/Cached/CoreC.lean:369-376` — **`proj_nodes_i` refines
`projNodesI`** at the cited `List.range nF` (`core_c.rs:717`). -/
theorem proj_nodes_i_refines {t : name.Name} {b : expr.Expr} {n_f : Std.U64}
    (ht : NameWF t) (hb : ExprWF b) :
    SimP (fun r => (pure (absExprs r) : ConLeche.Cached.CheckCM (List ConLeche.Cached.ExprC)))
      ExprsWF
      (cached.core_c.proj_nodes_i t b n_f 0#u64 (alloc.vec.Vec.new expr.Expr))
      (ConLeche.Cached.projNodesI (absName t) (absExpr b) (List.range n_f.val)) := by
  intro r h
  obtain ⟨habs, hwf⟩ := proj_nodes_i_abs n_f.val t b n_f 0#u64
    (alloc.vec.Vec.new expr.Expr) r ht hb ExprOps.exprsWF_new (by simp) h
  refine ⟨?_, hwf⟩
  dsimp only
  rw [projNodesI_pure, habs, List.range_eq_range']
  simp [absExprs]


/-! ## `proj_apps_fn_i` — the projection-function spelling

`ConLeche/Cached/CoreC.lean:356-367 projAppsFnI` (`core_c.rs:694`). -/

/-- `projAppsFnI` touches no state either: `mkAppNM` is
`pure (ExprC.mkAppN …)` (`Cached/StateC.lean:213-214`). -/
theorem projAppsFnI_pure (T : ConLeche.Name) (us' : List ConLeche.Level)
    (targs : List ConLeche.Cached.ExprC) (b : ConLeche.Cached.ExprC) :
    ∀ l : List Nat, ConLeche.Cached.projAppsFnI T us' targs b l
      = pure (l.map (fun i => ConLeche.Cached.ExprC.mkAppN
          (.const (ConLeche.projFnName T i) us') (targs ++ [b]))) := by
  intro l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [ConLeche.Cached.projAppsFnI, ih]; rfl

/-- The port's index loop. -/
theorem proj_apps_fn_i_abs (N : Nat) :
    ∀ (t : name.Name) (us2 : alloc.vec.Vec level.Level)
      (targs : alloc.vec.Vec expr.Expr) (b : expr.Expr) (n_f j : Std.U64)
      (out r : alloc.vec.Vec expr.Expr),
      NameWF t → LevelsWF us2 → ExprsWF targs → ExprWF b → ExprsWF out →
      n_f.val - j.val = N →
      cached.core_c.proj_apps_fn_i t us2 targs b n_f j out = ok r →
      absExprs r = absExprs out ++ (List.range' j.val N).map
          (fun i => ConLeche.Cached.ExprC.mkAppN
            (.const (ConLeche.projFnName (absName t) i) (absLevels us2))
            (absExprs targs ++ [absExpr b]))
        ∧ ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t us2 targs b n_f j out r ht hus2 htargs hb hout hN h
    unfold cached.core_c.proj_apps_fn_i at h
    split at h
    · rename_i hge
      have : N = 0 := by scalar_tac
      subst this
      rw [← Result.ok_injective h]
      exact ⟨by simp, hout⟩
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, v, hv, hd, hhd, v1, hv1, v2, hv2, spine, hspine,
        e, he, out1, hpush, i1, hi1, hrec⟩ := h
      obtain ⟨hnabs, hnwf⟩ := ConRon.Refine.proj_fn_name_refines ht hn
      have hvv : v = us2 := Env.levels_copy_refines hv
      rw [hvv] at hhd
      have hv1v : v1 = targs := Env.exprs_copy_refines hv1
      rw [hv1v] at hspine
      obtain ⟨hv2abs, hv2wf⟩ := CoreK.expr_singleton_refines hb hv2
      obtain ⟨hspabs, hspwf⟩ := CoreK.append_exprs_refines htargs hv2wf hspine
      rw [StateC.mk_app_n_m_eq] at he
      obtain ⟨heabs, hewf⟩ := ExprOpsC.mk_app_n_refines
        (ExprWF.mk_const hnwf hus2 hhd) hspwf he
      have hi1v : i1.val = j.val + 1 := HashMap.uscalar_add_eq hi1
      have hNpos : N = (n_f.val - i1.val) + 1 := by omega
      have heabs' : absExpr e = ConLeche.Cached.ExprC.mkAppN
          (.const (ConLeche.projFnName (absName t) j.val) (absLevels us2))
          (absExprs targs ++ [absExpr b]) := by
        rw [heabs, Expr.mk_const_refines hhd, hnabs, hspabs, hv2abs]
      have hout1 : absExprs out1 = absExprs out ++ [absExpr e] := by
        rw [absExprs, vec_push_val hpush]; simp [absExprs]
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hpush] at hx
        rcases List.mem_append.1 hx with h1 | h1
        · exact hout x h1
        · rw [List.mem_singleton.1 h1]; exact hewf
      obtain ⟨habs, hwf⟩ := ih (n_f.val - i1.val) (by omega) t us2 targs b n_f i1
        out1 r ht hus2 htargs hb hout1wf rfl hrec
      refine ⟨?_, hwf⟩
      rw [habs, hout1, hNpos, hi1v, List.range'_succ, heabs']
      simp

/-- `ConLeche/Cached/CoreC.lean:356-367` — **`proj_apps_fn_i` refines
`projAppsFnI`** at the cited `List.range nF` (`core_c.rs:694`). -/
theorem proj_apps_fn_i_refines {t : name.Name} {us2 : alloc.vec.Vec level.Level}
    {targs : alloc.vec.Vec expr.Expr} {b : expr.Expr} {n_f : Std.U64}
    (ht : NameWF t) (hus2 : LevelsWF us2) (htargs : ExprsWF targs) (hb : ExprWF b) :
    SimP (fun r => (pure (absExprs r) : ConLeche.Cached.CheckCM (List ConLeche.Cached.ExprC)))
      ExprsWF
      (cached.core_c.proj_apps_fn_i t us2 targs b n_f 0#u64 (alloc.vec.Vec.new expr.Expr))
      (ConLeche.Cached.projAppsFnI (absName t) (absLevels us2) (absExprs targs)
        (absExpr b) (List.range n_f.val)) := by
  intro r h
  obtain ⟨habs, hwf⟩ := proj_apps_fn_i_abs n_f.val t us2 targs b n_f 0#u64
    (alloc.vec.Vec.new expr.Expr) r ht hus2 htargs hb ExprOps.exprsWF_new (by simp) h
  refine ⟨?_, hwf⟩
  dsimp only
  rw [projAppsFnI_pure, habs, List.range_eq_range']
  simp [absExprs]

/-! ## `proj_apps_i` — the fabricated projections of a structure-eta spine

`ConLeche/Cached/CoreC.lean:378-386 projAppsI` (`core_c.rs:737`).  The cited
`(Tn T : Name)` pair is one parameter in the port: the two are the same name at
every call site (the retired arena's interned/raw split). -/

/-- `ConLeche/Cached/CoreC.lean:378-386` — **`proj_apps_i` refines
`projAppsI`**: the tower spelling at an all-tower slot family, the
projection-function spelling otherwise. -/
theorem proj_apps_i_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfwf : FEnvWF fe) (hfrel : FEnvRel fe lfe) {t : name.Name}
    {us2 : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} {n_f : Std.U64}
    (ht : NameWF t) (hus2 : LevelsWF us2) (htargs : ExprsWF targs) (hb : ExprWF b) :
    SimP (fun r => (pure (absExprs r) : ConLeche.Cached.CheckCM (List ConLeche.Cached.ExprC)))
      ExprsWF
      (cached.core_c.proj_apps_i fe t us2 targs b n_f)
      (ConLeche.Cached.projAppsI lfe (absName t) (absName t) (absLevels us2)
        (absExprs targs) (absExpr b) n_f.val) := by
  intro r h
  rw [cached.core_c.proj_apps_i] at h
  obtain ⟨bt, hbt, h⟩ := bind_eq_ok_iff.mp h
  have hbtabs := ConRon.Refine.tower_slots_all_f_refines (FindAgree.of_rel hfrel hfwf)
    (FindWF.of_wf hfwf) ht hbt
  rw [ConLeche.Cached.projAppsI, ← hbtabs]
  split at h
  · rename_i hbt1
    rw [if_pos hbt1]
    exact proj_nodes_i_refines ht hb r h
  · rename_i hbt1
    rw [if_neg hbt1]
    exact proj_apps_fn_i_refines ht hus2 htargs hb r h

/-! ## Running a `CheckCM` action whose `run` is known

The three facts that compose a `do` block on the con-leche side.  `Sim`/`SimS`
hand back `(g lfe).run lst = .ok (A r, lst')`; `run_bind` is what puts that into
the next step's shape. -/

/-- `pure` at `CheckCM`. -/
@[local simp] theorem run_pure {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl

/-- One `bind` at a known first step. -/
theorem run_bind {α β : Type} (m : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) {lst lst1 : ConLeche.Cached.CState} {a : α}
    (h : m.run lst = .ok (a, lst1)) : (m >>= f).run lst = (f a).run lst1 := by
  show Except.bind (m lst) _ = _
  rw [show m lst = .ok (a, lst1) from h]
  rfl

/-! ## `def_eq_list_i` — pairwise definitional equality of two spines

`ConLeche/Cached/CoreC.lean:201-209 defEqListI` (`core_c.rs:432`, `:449`).  The
cited `[], []` arm is "both exhausted", the cons arm is "both in range" and the
wildcard is the length mismatch; the port's one cursor `i` runs both `Vec`s, so
the correspondence is the pair of suffixes at `i`. -/

/-- The index recursion behind `def_eq_list_i`, at the cursor `i`. -/
theorem def_eq_list_i_from_aux {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) (N : Nat) :
    ∀ (xs ys : alloc.vec.Vec expr.Expr) (i : Std.Usize),
      ExprsWF xs → ExprsWF ys → xs.val.length - i.val = N →
      Sim id (fun _ => True)
        (fun st fe => cached.core_c.def_eq_list_i_from mode fuel st fe d xs ys i)
        (fun lfe => ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
          ((absExprs xs).drop i.val) ((absExprs ys).drop i.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs ys i hxs hys hN fe lfe hfe hfrel st r st' hwf hok lst hrel
    have hxl : (absExprs xs).length = xs.val.length := by simp [absExprs]
    have hyl : (absExprs ys).length = ys.val.length := by simp [absExprs]
    have hlx := alloc.vec.Vec.len_val xs
    have hly := alloc.vec.Vec.len_val ys
    unfold cached.core_c.def_eq_list_i_from at hok
    dsimp only at hok
    split at hok
    · -- `i ≥ xs.len()`: the cited `[], …` arms
      rename_i hge1
      have hgex : xs.val.length ≤ i.val := by scalar_tac
      have hdx : (absExprs xs).drop i.val = [] :=
        List.drop_eq_nil_of_le (by rw [hxl]; exact hgex)
      split at hok
      · -- `i ≥ ys.len()` too: `[], [] => pure true`
        rename_i hge2
        have hdy : (absExprs ys).drop i.val = [] :=
          List.drop_eq_nil_of_le (by rw [hyl]; scalar_tac)
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, trivial⟩
        rw [hdx, hdy]
        simp [ConLeche.Cached.defEqListI]
      · -- `i < ys.len()`: the length mismatch
        rename_i hlt2
        have hlty : i.val < ys.val.length := by scalar_tac
        have hdy : (absExprs ys).drop i.val
            = (absExprs ys)[i.val] :: (absExprs ys).drop (i.val + 1) :=
          List.drop_eq_getElem_cons (by rw [hxl] at *; omega)
        split at hok
        · rename_i hlt1; exact absurd hlt1 (by scalar_tac)
        · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hdx, hdy]
          simp [ConLeche.Cached.defEqListI]
    · -- `i < xs.len()`
      rename_i hlt1
      have hltx : i.val < xs.val.length := by scalar_tac
      split at hok
      · rename_i hlt1'
        split at hok
        · -- both in range: the cited cons arm
          rename_i hlt2
          have hlty : i.val < ys.val.length := by scalar_tac
          simp only [bind_eq_ok_iff] at hok
          obtain ⟨x, hxi, y, hyi, ⟨rr, st1⟩, hdq, hok⟩ := hok
          obtain ⟨-, hxwf, hdx⟩ := ExprOps.vec_index_expr hxs hxi
          obtain ⟨-, hywf, hdy⟩ := ExprOps.vec_index_expr hys hyi
          cases rr with
          | Err err => simp at hok
          | Ok bq =>
            -- the destructuring bind leaves a `let (r, st1) := (r, st1)` that
            -- `split` cannot see through; this `replace` is the iota step
            replace hok : (if bq = true then
                  (do let i5 ← i + 1#usize
                      cached.core_c.def_eq_list_i_from mode fuel st1 fe d xs ys i5)
                else ok (core.result.Result.Ok bq, st1))
                = ok (core.result.Result.Ok r, st') := hok
            obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
              (hw.defeqSim d hxwf hywf).apply hwf hfe hdq hrel hfrel
            rw [hdx, hdy]
            simp only [ConLeche.Cached.defEqListI]
            rw [run_bind _ _ (by simpa using hrun1)]
            split at hok
            · -- the pair agrees: on to the next index
              rename_i hbq
              subst hbq
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨i5, hi5, hok⟩ := hok
              have hi5v : i5.val = i.val + 1 := HashMap.uscalar_add_eq hi5
              have hlt : xs.val.length - i5.val < N := by omega
              obtain ⟨lst', hrun', hrel', hwf', -⟩ :=
                ih (xs.val.length - i5.val) hlt xs ys i5 hxs hys rfl fe lfe hfe hfrel
                  st1 r st' hwf1 hok lst1 hrel1
              refine ⟨lst', ?_, hrel', hwf', trivial⟩
              rw [if_pos rfl, ← hi5v]
              exact hrun'
            · -- the pair disagrees: `pure false`
              rename_i hbq
              have hbqf : bq = false := by simpa using hbq
              subst hbqf
              simp only [Result.ok.injEq, Prod.mk.injEq,
                core.result.Result.Ok.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst1, ?_, hrel1, hwf1, trivial⟩
              rw [if_neg (by simp)]
              rfl
        · -- `i ≥ ys.len()`: the length mismatch
          rename_i hge2
          have hdx : (absExprs xs).drop i.val
              = (absExprs xs)[i.val] :: (absExprs xs).drop (i.val + 1) :=
            List.drop_eq_getElem_cons (by rw [hxl]; exact hltx)
          have hdy : (absExprs ys).drop i.val = [] :=
            List.drop_eq_nil_of_le (by rw [hyl]; scalar_tac)
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hdx, hdy]
          simp [ConLeche.Cached.defEqListI]
      · rename_i hge1'; exact absurd hge1' (by scalar_tac)

/-- `ConLeche/Cached/CoreC.lean:201-209` — **`def_eq_list_i_from` refines
`defEqListI`** at the two suffixes the cursor names (`core_c.rs:449`). -/
theorem def_eq_list_i_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {xs ys : alloc.vec.Vec expr.Expr}
    (hxs : ExprsWF xs) (hys : ExprsWF ys) (i : Std.Usize) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.def_eq_list_i_from mode fuel st fe d xs ys i)
      (fun lfe => ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
        ((absExprs xs).drop i.val) ((absExprs ys).drop i.val)) :=
  def_eq_list_i_from_aux hw d _ xs ys i hxs hys rfl

/-- `ConLeche/Cached/CoreC.lean:201-209` — **`def_eq_list_i` refines
`defEqListI`** (`core_c.rs:432`): the `i = 0` wrapper. -/
theorem def_eq_list_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {xs ys : alloc.vec.Vec expr.Expr}
    (hxs : ExprsWF xs) (hys : ExprsWF ys) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.def_eq_list_i mode fuel st fe d xs ys)
      (fun lfe => ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
        (absExprs xs) (absExprs ys)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.def_eq_list_i at hok
  dsimp only at hok
  have := (def_eq_list_i_from_refines hw d hxs hys 0#usize).apply hwf hfe hok hrel hfrel
  simpa using this

/-! ## `iota_certs_i` — certifying a spine against a recursor telescope

`ConLeche/Cached/CoreC.lean:168-197 iotaCertsIAux`/`iotaCertsI`
(`core_c.rs:358`, `:415`).  The cited definition matches on the argument list
and then on the telescope's head; these four identities name its arms, so that
the port's `match ty.0.kind` can be answered one arm at a time without
rewriting `absExpr ty` out of the `instListM` calls. -/

/-- The exhausted spine. -/
theorem iotaCertsIAux_nil {r : ConLeche.Cached.CoreFnsI} {fe : ConLeche.FEnv}
    {depth : Nat} {lic : Bool} {ty : ConLeche.Cached.ExprC}
    {acc : List ConLeche.Cached.ExprC} :
    ConLeche.Cached.iotaCertsIAux r fe depth lic ty acc [] = pure true := by
  simp [ConLeche.Cached.iotaCertsIAux]

/-- A telescope head that is neither `∀` nor a raw `bvar`: the cited wildcard. -/
theorem iotaCertsIAux_dead {r : ConLeche.Cached.CoreFnsI} {fe : ConLeche.FEnv}
    {depth : Nat} {lic : Bool} {ty : ConLeche.Cached.ExprC}
    {acc : List ConLeche.Cached.ExprC}
    {arg : ConLeche.Cached.ExprC} {rest : List ConLeche.Cached.ExprC}
    (h1 : ∀ dom body mb, ty ≠ .forallE dom body mb) (h2 : ∀ k, ty ≠ .bvar k) :
    ConLeche.Cached.iotaCertsIAux r fe depth lic ty acc (arg :: rest) = pure false := by
  cases ty with
  | bvar k => exact absurd rfl (h2 k)
  | forallE dom body mb => exact absurd rfl (h1 dom body mb)
  | _ => simp [ConLeche.Cached.iotaCertsIAux]

/-- A raw `bvar` head at an empty accumulator: the cited `[] => pure false`. -/
theorem iotaCertsIAux_bvar_nil {r : ConLeche.Cached.CoreFnsI} {fe : ConLeche.FEnv}
    {depth : Nat} {lic : Bool} {ty : ConLeche.Cached.ExprC} {k : Nat}
    {arg : ConLeche.Cached.ExprC} {rest : List ConLeche.Cached.ExprC}
    (hty : ty = .bvar k) :
    ConLeche.Cached.iotaCertsIAux r fe depth lic ty [] (arg :: rest) = pure false := by
  subst hty; simp [ConLeche.Cached.iotaCertsIAux]

/-- A raw `bvar` head at a non-empty accumulator: substitute and re-enter (the
fold semantics).  `ty` stays on the right so that `instListM`'s argument is the
caller's. -/
theorem iotaCertsIAux_bvar_cons {r : ConLeche.Cached.CoreFnsI} {fe : ConLeche.FEnv}
    {depth : Nat} {lic : Bool} {ty : ConLeche.Cached.ExprC} {k : Nat}
    {a : ConLeche.Cached.ExprC} {acc : List ConLeche.Cached.ExprC}
    {arg : ConLeche.Cached.ExprC} {rest : List ConLeche.Cached.ExprC}
    (hty : ty = .bvar k) :
    ConLeche.Cached.iotaCertsIAux r fe depth lic ty (a :: acc) (arg :: rest)
      = (do let ty' ← ConLeche.Cached.instListM ty (a :: acc)
            ConLeche.Cached.iotaCertsIAux r fe depth lic ty' [] (arg :: rest)) := by
  subst hty; simp [ConLeche.Cached.iotaCertsIAux]

/-- A `∀` head: the cited licensed-skip test and the three-step certificate. -/
theorem iotaCertsIAux_forallE {r : ConLeche.Cached.CoreFnsI} {fe : ConLeche.FEnv}
    {depth : Nat} {lic : Bool} {ty dom body : ConLeche.Cached.ExprC}
    {mb : ConLeche.BinderMeta} {acc : List ConLeche.Cached.ExprC}
    {arg : ConLeche.Cached.ExprC} {rest : List ConLeche.Cached.ExprC}
    (hty : ty = .forallE dom body mb) :
    ConLeche.Cached.iotaCertsIAux r fe depth lic ty acc (arg :: rest)
      = (if lic && mb.pw.isNever then
            ConLeche.Cached.iotaCertsIAux r fe depth lic body (arg :: acc) rest
          else do
            let dom' ← ConLeche.Cached.instListM dom acc
            let ta ← r.inferIO depth arg
            if ← r.defeq depth ta dom' then
              ConLeche.Cached.iotaCertsIAux r fe depth lic body (arg :: acc) rest
            else pure false) := by
  subst hty; simp [ConLeche.Cached.iotaCertsIAux]

/-- The port's accumulator loop, at the cited `termination_by (args.length,
acc.length)`: a strong induction on the arguments still to come, and inside it
one on the accumulator (the `bvar` arm empties it without consuming an
argument). -/
theorem iota_certs_i_aux_aux (hsc : StateCOpen) {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) (N : Nat) :
    ∀ (M : Nat) (lic : Bool) (ty : expr.Expr) (acc args : alloc.vec.Vec expr.Expr)
      (i : Std.Usize), ExprWF ty → ExprsWF acc → ExprsWF args →
      args.val.length - i.val = N → acc.val.length = M →
      Sim id (fun _ => True)
        (fun st fe => cached.core_c.iota_certs_i_aux mode fuel st fe d lic ty acc args i)
        (fun lfe => ConLeche.Cached.iotaCertsIAux (knot mode lfe fuel.val) lfe d.val lic
          (absExpr ty) (absExprs acc) ((absExprs args).drop i.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ihM =>
      intro lic ty acc args i hty hacc hargs hN hM fe lfe hfe hfrel st r st' hwf hok lst hrel
      dsimp only
      have hla := alloc.vec.Vec.len_val args
      have hlc := alloc.vec.Vec.len_val acc
      unfold cached.core_c.iota_certs_i_aux at hok
      dsimp only at hok
      split at hok
      · -- `i ≥ args.len()`: the cited `_, _, [] => pure true`
        rename_i hge
        have hdarg : (absExprs args).drop i.val = [] :=
          List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, trivial⟩
        rw [hdarg, iotaCertsIAux_nil]
        rfl
      · rename_i hge
        have hlti : i.val < args.val.length := by scalar_tac
        obtain ⟨ax, hax⟩ : ∃ ax, (absExprs args).drop i.val
            = ax :: (absExprs args).drop (i.val + 1) :=
          ⟨_, List.drop_eq_getElem_cons (by simp only [absExprs, List.length_map]; exact hlti)⟩
        simp only [arc_deref_eq, bind_tc_ok] at hok
        split at hok
        · -- `.bvar`: the fold step
          rename_i hk
          have hkabs : ∃ k, absExpr ty = ConLeche.Expr.bvar k := by
            rw [CoreK.absExpr_kind ty, hk]; exact ⟨_, rfl⟩
          obtain ⟨kk, hk'⟩ := hkabs
          split at hok
          · -- the accumulator is empty: the cited `[] => pure false`
            rename_i hz
            have haccnil : absExprs acc = [] := by
              simp only [absExprs, HashMap.vec_len_eq_zero_iff.mp hz, List.map_nil]
            simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst, ?_, hrel, hwf, trivial⟩
            rw [hax, haccnil, iotaCertsIAux_bvar_nil hk']
            rfl
          · -- substitute the accumulator and re-enter
            rename_i hz
            have hMpos : 0 < acc.val.length := by
              rcases Nat.eq_zero_or_pos acc.val.length with h0 | h0
              · exact absurd (HashMap.vec_len_eq_zero_iff.mpr
                  (List.eq_nil_of_length_eq_zero h0)) hz
              · exact h0
            obtain ⟨a, acc', hacc'⟩ : ∃ a acc', absExprs acc = a :: acc' := by
              cases hcc : absExprs acc with
              | nil =>
                exfalso
                have : (absExprs acc).length = 0 := by rw [hcc]; rfl
                simp only [absExprs, List.length_map] at this
                omega
              | cons a t => exact ⟨a, t, rfl⟩
            simp only [bind_eq_ok_iff] at hok
            obtain ⟨⟨ty2, st1⟩, hinst, hok⟩ := hok
            replace hok : cached.core_c.iota_certs_i_aux mode fuel st1 fe d lic ty2
                (alloc.vec.Vec.new expr.Expr) args i
                = ok (core.result.Result.Ok r, st') := hok
            obtain ⟨lst1, hrun1, hrel1, hwf1, -, hty2⟩ :=
              StateC.inst_list_m_refines hsc.instList hwf hty hacc hinst lst hrel
                (hsc.instSize st lst hrel)
            obtain ⟨lst', hrun', hrel', hwf', -⟩ :=
              ihM 0 (by omega) lic ty2 (alloc.vec.Vec.new expr.Expr) args i hty2
                ExprOps.exprsWF_new hargs hN rfl fe lfe hfe hfrel st1 r st' hwf1 hok lst1 hrel1
            refine ⟨lst', ?_, hrel', hwf', trivial⟩
            rw [hax, hacc', iotaCertsIAux_bvar_cons hk']
            rw [hacc'] at hrun1
            rw [run_bind _ _ (by simpa using hrun1)]
            simpa [hax] using hrun'
        · -- `.fvar`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.sort`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.const`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.app`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.lam`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.forallE`: the cited `∀` head
          rename_i dm bd mb hk
          have hkabs : absExpr ty = ConLeche.Expr.forallE (absExpr dm) (absExpr bd)
              (absBinderMeta mb) := by rw [CoreK.absExpr_kind ty, hk]; rfl
          obtain ⟨hdomwf, hbodywf, hmbwf⟩ := CoreK.ExprWF.forallE_children hty hk
          simp only [expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at hok
          obtain ⟨e, hei, acc2, hcons, hok⟩ := hok
          obtain ⟨-, hewf, hdx⟩ := ExprOps.vec_index_expr hargs hei
          obtain ⟨hacc2abs, hacc2wf⟩ := ExprOps.cons_expr_refines hewf hacc hcons
          rw [hdx, iotaCertsIAux_forallE hkabs]
          split at hok
          · -- a licensed walk
            rename_i hlic
            subst hlic
            simp only [bind_eq_ok_iff] at hok
            obtain ⟨bnv, hbnv, hok⟩ := hok
            have hbnvabs : bnv = (absPropWhen mb.pw).isNever := PropWhen.is_never_refines hbnv
            split at hok
            · -- a `.never` slot: skipped outright
              rename_i hb
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨i2, hi2, hok⟩ := hok
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              obtain ⟨lst', hrun', hrel', hwf', -⟩ :=
                ihN (args.val.length - i2.val) (by omega) acc2.val.length true bd acc2 args i2
                  hbodywf hacc2wf hargs rfl rfl fe lfe hfe hfrel st r st' hwf hok lst hrel
              refine ⟨lst', ?_, hrel', hwf', trivial⟩
              rw [if_pos (by simp [absBinderMeta, ← hbnvabs, hb])]
              simpa [hacc2abs, hi2v] using hrun'
            · -- the slot is certified
              rename_i hb
              have hbf : bnv = false := by simpa using hb
              rw [if_neg (by simp [absBinderMeta, ← hbnvabs, hbf])]
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨⟨dom2, st1⟩, hinst, hok⟩ := hok
              replace hok : (do
                  let (rr, st2) ← cached.core_c.infer_io mode fuel st1 fe d e
                  match rr with
                  | core.result.Result.Ok ta =>
                    (do let (r1, st3) ← cached.core_c.defeq mode fuel st2 fe d ta dom2
                        match r1 with
                        | core.result.Result.Ok b1 =>
                          if b1 = true then
                            (do let i2 ← i + 1#usize
                                cached.core_c.iota_certs_i_aux mode fuel st3 fe d true bd
                                  acc2 args i2)
                          else ok (r1, st3)
                        | core.result.Result.Err _ => ok (r1, st3))
                  | core.result.Result.Err err =>
                    ok (core.result.Result.Err err, st2))
                  = ok (core.result.Result.Ok r, st') := hok
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨⟨rr, st2⟩, hio, hok⟩ := hok
              obtain ⟨lst1, hrun1, hrel1, hwf1, -, hdom2⟩ :=
                StateC.inst_list_m_refines hsc.instList hwf hdomwf hacc hinst lst hrel
                  (hsc.instSize st lst hrel)
              rw [run_bind _ _ (by simpa using hrun1)]
              cases rr with
              | Err err => simp at hok
              | Ok ta =>
                replace hok : (do
                    let (r1, st3) ← cached.core_c.defeq mode fuel st2 fe d ta dom2
                    match r1 with
                    | core.result.Result.Ok b1 =>
                      if b1 = true then
                        (do let i2 ← i + 1#usize
                            cached.core_c.iota_certs_i_aux mode fuel st3 fe d true bd acc2
                              args i2)
                      else ok (r1, st3)
                    | core.result.Result.Err _ => ok (r1, st3))
                    = ok (core.result.Result.Ok r, st') := hok
                obtain ⟨lst2, hrun2, hrel2, hwf2, htawf⟩ :=
                  (hw.inferIOSim d hewf).apply hwf1 hfe hio hrel1 hfrel
                rw [run_bind _ _ hrun2]
                simp only [bind_eq_ok_iff] at hok
                obtain ⟨⟨r1, st3⟩, hdq, hok⟩ := hok
                cases r1 with
                | Err err => simp at hok
                | Ok b1 =>
                  replace hok : (if b1 = true then
                        (do let i2 ← i + 1#usize
                            cached.core_c.iota_certs_i_aux mode fuel st3 fe d true bd acc2
                              args i2)
                      else ok (core.result.Result.Ok b1, st3))
                      = ok (core.result.Result.Ok r, st') := hok
                  obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
                    (hw.defeqSim d htawf hdom2).apply hwf2 hfe hdq hrel2 hfrel
                  rw [run_bind _ _ (by simpa using hrun3)]
                  split at hok
                  · rename_i hb1
                    subst hb1
                    simp only [bind_eq_ok_iff] at hok
                    obtain ⟨i2, hi2, hok⟩ := hok
                    have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
                    obtain ⟨lst', hrun', hrel', hwf', -⟩ :=
                      ihN (args.val.length - i2.val) (by omega) acc2.val.length true bd acc2
                        args i2 hbodywf hacc2wf hargs rfl rfl fe lfe hfe hfrel st3 r st' hwf3
                        hok lst3 hrel3
                    refine ⟨lst', ?_, hrel', hwf', trivial⟩
                    rw [if_pos rfl]
                    simpa [hacc2abs, hi2v] using hrun'
                  · rename_i hb1
                    have hb1f : b1 = false := by simpa using hb1
                    subst hb1f
                    simp only [Result.ok.injEq, Prod.mk.injEq,
                      core.result.Result.Ok.injEq] at hok
                    obtain ⟨rfl, rfl⟩ := hok
                    refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
                    rw [if_neg (by simp)]
                    rfl
          · -- an unlicensed walk: every slot is certified
            rename_i hlic
            have hlicf : lic = false := by simpa using hlic
            subst hlicf
            rw [if_neg (by simp)]
            simp only [bind_eq_ok_iff] at hok
            obtain ⟨⟨dom2, st1⟩, hinst, hok⟩ := hok
            replace hok : (do
                let (rr, st2) ← cached.core_c.infer_io mode fuel st1 fe d e
                match rr with
                | core.result.Result.Ok ta =>
                  (do let (r1, st3) ← cached.core_c.defeq mode fuel st2 fe d ta dom2
                      match r1 with
                      | core.result.Result.Ok b1 =>
                        if b1 = true then
                          (do let i2 ← i + 1#usize
                              cached.core_c.iota_certs_i_aux mode fuel st3 fe d false bd
                                acc2 args i2)
                        else ok (r1, st3)
                      | core.result.Result.Err _ => ok (r1, st3))
                | core.result.Result.Err err =>
                  ok (core.result.Result.Err err, st2))
                = ok (core.result.Result.Ok r, st') := hok
            simp only [bind_eq_ok_iff] at hok
            obtain ⟨⟨rr, st2⟩, hio, hok⟩ := hok
            obtain ⟨lst1, hrun1, hrel1, hwf1, -, hdom2⟩ :=
              StateC.inst_list_m_refines hsc.instList hwf hdomwf hacc hinst lst hrel
                (hsc.instSize st lst hrel)
            rw [run_bind _ _ (by simpa using hrun1)]
            cases rr with
            | Err err => simp at hok
            | Ok ta =>
              replace hok : (do
                  let (r1, st3) ← cached.core_c.defeq mode fuel st2 fe d ta dom2
                  match r1 with
                  | core.result.Result.Ok b1 =>
                    if b1 = true then
                      (do let i2 ← i + 1#usize
                          cached.core_c.iota_certs_i_aux mode fuel st3 fe d false bd acc2
                            args i2)
                    else ok (r1, st3)
                  | core.result.Result.Err _ => ok (r1, st3))
                  = ok (core.result.Result.Ok r, st') := hok
              obtain ⟨lst2, hrun2, hrel2, hwf2, htawf⟩ :=
                (hw.inferIOSim d hewf).apply hwf1 hfe hio hrel1 hfrel
              rw [run_bind _ _ hrun2]
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨⟨r1, st3⟩, hdq, hok⟩ := hok
              cases r1 with
              | Err err => simp at hok
              | Ok b1 =>
                replace hok : (if b1 = true then
                      (do let i2 ← i + 1#usize
                          cached.core_c.iota_certs_i_aux mode fuel st3 fe d false bd acc2
                            args i2)
                    else ok (core.result.Result.Ok b1, st3))
                    = ok (core.result.Result.Ok r, st') := hok
                obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
                  (hw.defeqSim d htawf hdom2).apply hwf2 hfe hdq hrel2 hfrel
                rw [run_bind _ _ (by simpa using hrun3)]
                split at hok
                · rename_i hb1
                  subst hb1
                  simp only [bind_eq_ok_iff] at hok
                  obtain ⟨i2, hi2, hok⟩ := hok
                  have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
                  obtain ⟨lst', hrun', hrel', hwf', -⟩ :=
                    ihN (args.val.length - i2.val) (by omega) acc2.val.length false bd acc2
                      args i2 hbodywf hacc2wf hargs rfl rfl fe lfe hfe hfrel st3 r st' hwf3
                      hok lst3 hrel3
                  refine ⟨lst', ?_, hrel', hwf', trivial⟩
                  rw [if_pos rfl]
                  simpa [hacc2abs, hi2v] using hrun'
                · rename_i hb1
                  have hb1f : b1 = false := by simpa using hb1
                  subst hb1f
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
                  rw [if_neg (by simp)]
                  rfl
        · -- `.letE`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.lit`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl
        · -- `.proj`
          rename_i hk
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hax, iotaCertsIAux_dead (by simp [CoreK.absExpr_kind ty, hk]) (by simp [CoreK.absExpr_kind ty, hk])]
          rfl

/-- `ConLeche/Cached/CoreC.lean:168-194` — **`iota_certs_i_aux` refines
`iotaCertsIAux`** (`core_c.rs:358`). -/
theorem iota_certs_i_aux_refines (hsc : StateCOpen) {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) (lic : Bool) {ty : expr.Expr}
    {acc args : alloc.vec.Vec expr.Expr} (i : Std.Usize)
    (hty : ExprWF ty) (hacc : ExprsWF acc) (hargs : ExprsWF args) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i_aux mode fuel st fe d lic ty acc args i)
      (fun lfe => ConLeche.Cached.iotaCertsIAux (knot mode lfe fuel.val) lfe d.val lic
        (absExpr ty) (absExprs acc) ((absExprs args).drop i.val)) :=
  iota_certs_i_aux_aux hsc hw d _ _ lic ty acc args i hty hacc hargs rfl rfl

/-- `ConLeche/Cached/CoreC.lean:195-199` — **`iota_certs_i` refines
`iotaCertsI`** (`core_c.rs:415`): the loop at the empty accumulator and the
first argument. -/
theorem iota_certs_i_refines (hsc : StateCOpen) {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) (lic : Bool) {ty : expr.Expr}
    {args : alloc.vec.Vec expr.Expr} (hty : ExprWF ty) (hargs : ExprsWF args) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i mode fuel st fe d lic ty args)
      (fun lfe => ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val lic
        (absExpr ty) (absExprs args)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.iota_certs_i at hok
  dsimp only at hok
  have := (iota_certs_i_aux_refines hsc hw d lic 0#usize hty ExprOps.exprsWF_new hargs).apply
    hwf hfe hok hrel hfrel
  simpa [ConLeche.Cached.iotaCertsI] using this


/-! ## Peeling a destructuring bind

Aeneas writes every state-passing call as `let (r, st) ← f …`, whose
continuation is a `match` on a pair; `simp` will not see through the iota step
that a `cases` on the pair leaves behind (`Refine/CoreKVec.lean:216` says the
same about `leaf_contains_from`).  This lemma does it once: its `f a s` is a
Miller pattern, so unification beta-reduces the continuation for free. -/
theorem bind_pair_eq_ok {α β γ : Type} {x : Result (α × β)}
    {f : α → β → Result γ} {r : γ}
    (h : (do let (a, s) ← x; f a s) = ok r) :
    ∃ a s, x = ok (a, s) ∧ f a s = ok r := by
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  exact ⟨p.1, p.2, hx, h⟩

/-! ## `proof_irrel_i` — proof irrelevance

`ConLeche/Cached/CoreC.lean:240-268 proofIrrelI` (`core_c.rs:568`).  Its second
half — the two `Prop` legs — is written out *verbatim* again inside
`propIrrelI` (`:344-354`), so the port hoists it into `prop_legs_i`
(`core_c.rs:605`) and both twins call it.  `propLegsI` below is that block,
written once: it is the cited definition's own tail, so `proof_irrel_i`'s
`else` arm meets it by `rfl`. -/

/-- `ConLeche/Cached/CoreC.lean:252-268` (and `:344-354`) — the two `Prop`
legs: the type of `ta` whnfs to a sort that is `Prop`, and so does the type of
the type of `b`.  Both comparisons are `isEquivLM`, i.e. through `eqvC`. -/
def propLegsI (r : ConLeche.Cached.CoreFnsI) (depth : Nat)
    (ta b : ConLeche.Cached.ExprC) : ConLeche.Cached.CheckCM Bool := do
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← ConLeche.liftFueled "level comparison" (← ConLeche.Cached.isEquivLM uT z)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← ConLeche.liftFueled "level comparison" (← ConLeche.Cached.isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- `core_k::lift_fueled` succeeded, so the fuelled option was `some`. -/
theorem lift_fueled_some {o : Option Bool} {b : Bool}
    (h : core_k.lift_fueled o = ok (.Ok b)) : o = some b := by
  have hb := CoreK.lift_fueled_refines h
  cases o with
  | none => simp [ConLeche.liftFueled] at hb
  | some x => simpa [ConLeche.liftFueled] using hb

/-- `liftFueled` at a `some`, in `CheckCM`. -/
theorem run_liftFueled {α : Type} {o : Option α} {a : α} (what : String)
    (lst : ConLeche.Cached.CState) (h : o = some a) :
    (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM) what o).run lst = .ok (a, lst) := by
  subst h; rfl

/-- `ConLeche/Cached/CoreC.lean:252-268` — **`prop_legs_i` refines the two
`Prop` legs** (`core_c.rs:605`). -/
theorem prop_legs_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {ta b : expr.Expr}
    (hta : ExprWF ta) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.prop_legs_i mode fuel st fe d ta b)
      (fun lfe => propLegsI (knot mode lfe fuel.val) d.val (absExpr ta) (absExpr b)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.prop_legs_i at hok
  dsimp only at hok
  rw [propLegsI]
  obtain ⟨rr, st1, hio, hok⟩ := bind_pair_eq_ok hok
  cases rr with
  | Err err => simp at hok
  | Ok tta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httawf⟩ :=
      (hw.inferIOSim d hta).apply hwf hfe hio hrel hfrel
    rw [run_bind _ _ hrun1]
    obtain ⟨r1, st2, hwh, hok⟩ := bind_pair_eq_ok hok
    cases r1 with
    | Err err => simp at hok
    | Ok wtta =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwttawf⟩ :=
        (hw.whnfSim d httawf).apply hwf1 hfe hwh hrel1 hfrel
      rw [run_bind _ _ hrun2]
      simp only [arc_deref_eq, bind_tc_ok] at hok
      split at hok
      · -- `.bvar`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.fvar`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.sort`: the `Prop` test on the type of `ta`
        rename_i u_t hk
        have hkabs : absExpr wtta = ConLeche.Expr.sort (absLevel u_t) := by
          rw [CoreK.absExpr_kind wtta, hk]; rfl
        have hutwf : LevelWF u_t := CoreK.ExprWF.sort_child hwttawf hk
        simp only [hkabs]
        rw [run_bind _ _ (run_pure _ _)]
        obtain ⟨l, hl, hok⟩ := bind_eq_ok_iff.mp hok
        have hlabs : absLevel l = ConLeche.Level.zero := Level.zero_refines hl
        have hlwf : LevelWF l := LevelWF.zero hl
        obtain ⟨eq_a, st3, heqa, hok⟩ := bind_pair_eq_ok hok
        obtain ⟨lst3, hrun3, hrel3, hwf3⟩ :=
          StateC.is_equiv_l_m_refines hwf2 hutwf hlwf heqa lst2 hrel2
        rw [hlabs] at hrun3
        obtain ⟨r2, hlift, hok⟩ := bind_eq_ok_iff.mp hok
        cases r2 with
        | Err err => simp at hok
        | Ok ok_a =>
          have heqasome : eq_a = some ok_a := lift_fueled_some hlift
          rw [run_bind _ _ hrun3, run_bind _ _ (run_liftFueled _ _ heqasome)]
          obtain ⟨r3, st4, hio2, hok⟩ := bind_pair_eq_ok hok
          cases r3 with
          | Err err => simp at hok
          | Ok tb =>
            obtain ⟨lst4, hrun4, hrel4, hwf4, htbwf⟩ :=
              (hw.inferIOSim d hb).apply hwf3 hfe hio2 hrel3 hfrel
            rw [run_bind _ _ hrun4]
            obtain ⟨r4, st5, hio3, hok⟩ := bind_pair_eq_ok hok
            cases r4 with
            | Err err => simp at hok
            | Ok ttb =>
              obtain ⟨lst5, hrun5, hrel5, hwf5, httbwf⟩ :=
                (hw.inferIOSim d htbwf).apply hwf4 hfe hio3 hrel4 hfrel
              rw [run_bind _ _ hrun5]
              obtain ⟨r5, st6, hwh2, hok⟩ := bind_pair_eq_ok hok
              cases r5 with
              | Err err => simp at hok
              | Ok wttb =>
                obtain ⟨lst6, hrun6, hrel6, hwf6, hwttbwf⟩ :=
                  (hw.whnfSim d httbwf).apply hwf5 hfe hwh2 hrel5 hfrel
                rw [run_bind _ _ hrun6]
                simp only at hok
                split at hok
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · -- `.sort`: the `Prop` test on the type of the type of `b`
                  rename_i v_t hk2
                  have hk2abs : absExpr wttb = ConLeche.Expr.sort (absLevel v_t) := by
                    rw [CoreK.absExpr_kind wttb, hk2]; rfl
                  have hvtwf : LevelWF v_t := CoreK.ExprWF.sort_child hwttbwf hk2
                  simp only [hk2abs]
                  rw [run_bind _ _ (run_pure _ _)]
                  obtain ⟨eq_b, st7, heqb, hok⟩ := bind_pair_eq_ok hok
                  obtain ⟨lst7, hrun7, hrel7, hwf7⟩ :=
                    StateC.is_equiv_l_m_refines hwf6 hvtwf hlwf heqb lst6 hrel6
                  rw [hlabs] at hrun7
                  obtain ⟨r6, hlift2, hok⟩ := bind_eq_ok_iff.mp hok
                  split at hok
                  · rename_i ok_b
                    have heqbsome : eq_b = some ok_b := lift_fueled_some hlift2
                    rw [run_bind _ _ hrun7, run_bind _ _ (run_liftFueled _ _ heqbsome)]
                    split at hok
                    · -- `ok_a` held: the verdict is `ok_b`
                      rename_i hoka
                      simp only [Result.ok.injEq, Prod.mk.injEq,
                        core.result.Result.Ok.injEq] at hok
                      refine ⟨lst7, ?_, hok.2 ▸ hrel7, hok.2 ▸ hwf7, trivial⟩
                      rw [hoka, ← hok.1]
                      rfl
                    · -- `ok_a` failed: the verdict is `ok_a`
                      rename_i hoka
                      have hokaf : ok_a = false := by simpa using hoka
                      simp only [Result.ok.injEq, Prod.mk.injEq,
                        core.result.Result.Ok.injEq] at hok
                      refine ⟨lst7, ?_, hok.2 ▸ hrel7, hok.2 ▸ hwf7, trivial⟩
                      rw [← hok.1, hokaf]
                      rfl
                  · rename_i err
                    simp at hok
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
                · rename_i hk2
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨lst6, ?_, hrel6, hwf6, trivial⟩
                  rw [CoreK.absExpr_kind wttb, hk2]; simp
      · -- `.const`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.app`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.lam`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.forallE`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.letE`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.lit`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp
      · -- `.proj`
        rename_i hk
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        rw [CoreK.absExpr_kind wtta, hk]; simp

/-- `ConLeche/Cached/CoreC.lean:240-268` — **`proof_irrel_i` refines
`proofIrrelI`** (`core_c.rs:568`): both sides' types whnf to the basis unit
type, or both sides' types' sorts are `Prop`. -/
theorem proof_irrel_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.proof_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.proofIrrelI (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.proof_irrel_i at hok
  dsimp only at hok
  rw [ConLeche.Cached.proofIrrelI]
  obtain ⟨rr, st1, hio, hok⟩ := bind_pair_eq_ok hok
  cases rr with
  | Err err => simp at hok
  | Ok ta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htawf⟩ :=
      (hw.inferIOSim d ha).apply hwf hfe hio hrel hfrel
    rw [run_bind _ _ hrun1]
    obtain ⟨r1, st2, hwh, hok⟩ := bind_pair_eq_ok hok
    cases r1 with
    | Err err => simp at hok
    | Ok wta =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwtawf⟩ :=
        (hw.whnfSim d htawf).apply hwf1 hfe hwh hrel1 hfrel
      rw [run_bind _ _ hrun2]
      obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1abs : b1 = ConLeche.Cached.isUnitLikeTyC lfe (absExpr wta) := by
        rw [CoreK.is_unit_like_ty_refines CoreK.pinned_punit_name
          CoreK.pinned_punit_rec_name (FindAgree.of_rel hfrel hfe) hwtawf hb1]
        rfl
      split at hok
      · -- the unit-like leg
        rename_i hb1t
        subst hb1t
        rw [run_bind _ _ (run_pure _ _), if_pos (by rw [← hb1abs])]
        obtain ⟨r2, st3, hio2, hok⟩ := bind_pair_eq_ok hok
        cases r2 with
        | Err err => simp at hok
        | Ok tb =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, htbwf⟩ :=
            (hw.inferIOSim d hb).apply hwf2 hfe hio2 hrel2 hfrel
          rw [run_bind _ _ hrun3]
          obtain ⟨r3, st4, hwh2, hok⟩ := bind_pair_eq_ok hok
          cases r3 with
          | Err err => simp at hok
          | Ok wtb =>
            obtain ⟨lst4, hrun4, hrel4, hwf4, hwtbwf⟩ :=
              (hw.whnfSim d htbwf).apply hwf3 hfe hwh2 hrel3 hfrel
            rw [run_bind _ _ hrun4]
            obtain ⟨b2, hb2, hok⟩ := bind_eq_ok_iff.mp hok
            have hb2abs : b2 = ConLeche.Cached.isUnitLikeTyC lfe (absExpr wtb) := by
              rw [CoreK.is_unit_like_ty_refines CoreK.pinned_punit_name
                CoreK.pinned_punit_rec_name (FindAgree.of_rel hfrel hfe) hwtbwf hb2]
              rfl
            simp only [Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst4, ?_, hrel4, hwf4, trivial⟩
            rw [run_bind _ _ (run_pure _ _), ← hb2abs]
            cases b2 <;> rfl
      · -- the `Prop` legs
        rename_i hb1f
        have hb1ff : b1 = false := by simpa using hb1f
        subst hb1ff
        rw [run_bind _ _ (run_pure _ _), if_neg (by rw [← hb1abs]; simp)]
        exact (prop_legs_i_refines hw d htawf hb).apply hwf2 hfe hok hrel2 hfrel

/-! ## `struct_eta_proj_certs_i` — the per-projection telescope certificates

`ConLeche/Cached/CoreC.lean:388-405 structEtaProjCertsI` (`core_c.rs:760`,
`:779`).  The cited `List Nat` is always `List.range nF`, so the port walks
`j = 0 … nF - 1` and the correspondence at the cursor is
`List.range' j (nF - j)`.  The cited `(TI T : Name)` pair is one parameter in
the port (the retired arena's interned/raw split). -/

/-- The index recursion behind `struct_eta_proj_certs_i`, at the cursor `j`. -/
theorem struct_eta_proj_certs_i_from_aux (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) (N : Nat) :
    ∀ (t : name.Name) (us2 : alloc.vec.Vec level.Level)
      (targs : alloc.vec.Vec expr.Expr) (b : expr.Expr)
      (lps_t : alloc.vec.Vec name.Name) (n_f j : Std.U64),
      NameWF t → LevelsWF us2 → ExprsWF targs → ExprWF b → NamesWF lps_t →
      n_f.val - j.val = N →
      Sim id (fun _ => True)
        (fun st fe => cached.core_c.struct_eta_proj_certs_i_from mode fuel st fe d t us2
          targs b lps_t n_f j)
        (fun lfe => ConLeche.Cached.structEtaProjCertsI (knot mode lfe fuel.val) lfe d.val
          (absName t) (absName t) (absLevels us2) (absExprs targs) (absExpr b)
          (absNames lps_t) (List.range' j.val N)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t us2 targs b lps_t n_f j ht hus2 htargs hb hlps hN fe lfe hfe hfrel st r st'
      hwf hok lst hrel
    dsimp only
    unfold cached.core_c.struct_eta_proj_certs_i_from at hok
    dsimp only at hok
    split at hok
    · -- `j ≥ n_f`: the cited `[] => pure true`
      rename_i hge
      have hN0 : N = 0 := by scalar_tac
      subst hN0
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact ⟨lst, rfl, hrel, hwf, trivial⟩
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      have hNs : N = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hNs, List.range'_succ]
      simp only [ConLeche.Cached.structEtaProjCertsI]
      obtain ⟨n, hn, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨hnabs, hnwf⟩ := ConRon.Refine.proj_fn_name_refines ht hn
      obtain ⟨o, hprobe, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨hoabs, howf⟩ := CoreK.rec_probe_refines (FindAgree.of_rel hfrel hfe)
        (FindWF.of_wf hfe) hnwf hprobe
      cases o with
      | none =>
        simp only [Option.map_none] at hoabs
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, trivial⟩
        rw [← hnabs]
        cases hf : lfe.find? (absName n) with
        | none => simp
        | some ci =>
          cases ci with
          | recInfo cv m p rs => rw [hf] at hoabs; simp [CoreK.recOf] at hoabs
          | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _
          | ctorInfo _ _ _ | projInfo _ => simp
      | some p =>
        obtain ⟨cvp, mI, rP, rules⟩ := p
        obtain ⟨hcvpwf, -⟩ := howf cvp mI rP rules rfl
        simp only [Option.map_some] at hoabs
        have hfind : lfe.find? (absName n)
            = some (.recInfo (absConstantVal cvp) mI.val rP.val (absRecRules rules)) := by
          cases hf : lfe.find? (absName n) with
          | none => rw [hf] at hoabs; simp [CoreK.recOf] at hoabs
          | some ci =>
            rw [hf] at hoabs
            cases ci with
            | recInfo cv m p rs =>
              simp only [CoreK.recOf, Option.some.injEq, Prod.mk.injEq] at hoabs
              obtain ⟨h1, h2, h3, h4⟩ := hoabs
              rw [h1, h2, h3, h4]
            | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _
            | ctorInfo _ _ _ | projInfo _ => simp [CoreK.recOf] at hoabs
        rw [← hnabs, hfind]
        simp only
        obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
        have hb1abs : b1 = decide (absNames cvp.level_params = absNames lps_t) :=
          CoreK.names_beq_refines hcvpwf.2.1 hlps hb1
        split at hok
        · -- the level parameters agree
          rename_i hb1t
          have hlpseq : absNames cvp.level_params = absNames lps_t := by
            apply of_decide_eq_true
            rw [← hb1abs]; exact hb1t
          obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨o1, hsp, hok⟩ := bind_eq_ok_iff.mp hok
          have hi1v : i1.val = targs.val.length := by
            have := ExprOps.usize_cast_u64_val (alloc.vec.Vec.len targs)
            have := alloc.vec.Vec.len_val targs
            simp only [lift_eq, Result.ok.injEq] at hi1
            scalar_tac
          have hi2v : i2.val = targs.val.length + 1 := by
            rw [HashMap.uscalar_add_eq hi2, hi1v]; rfl
          obtain ⟨hspabs, -⟩ := ExprOps.strip_pis_refines hcvpwf.2.2 hsp
          have htargslen : (absExprs targs).length = targs.val.length := by simp [absExprs]
          split at hok
          · -- the telescope has the right arity
            rename_i hsome
            have hstrip : ConLeche.Expr.stripPis ((absExprs targs).length + 1)
                (absExpr cvp.ty)
                = Option.map (fun p => (ExprOps.absBinders p.1, absExpr p.2)) o1 := by
              rw [htargslen, ← hi2v, ← hspabs]
            have hsomeL : ((absConstantVal cvp).type.stripPis
                ((absExprs targs).length + 1)).isSome = true := by
              simp only [absConstantVal, hstrip]
              cases o1 with
              | none => simp [core.option.Option.is_some] at hsome
              | some q => simp
            rw [if_pos ⟨hlpseq, hsomeL⟩]
            obtain ⟨rr, st1, hcty, hok⟩ := bind_pair_eq_ok hok
            cases rr with
            | Err err => simp at hok
            | Ok pty =>
              obtain ⟨lst1, hrun1, hrel1, hwf1, hptywf⟩ :=
                StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hnwf hus2
                  hcty lst lfe hrel hfrel (absName n)
              rw [run_bind _ _ (run_pure _ _), run_bind _ _ hrun1]
              obtain ⟨v, hv, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨v1, hv1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨spine, hspine, hok⟩ := bind_eq_ok_iff.mp hok
              have hvv : v = targs := Env.exprs_copy_refines hv
              rw [hvv] at hspine
              obtain ⟨hv1abs, hv1wf⟩ := CoreK.expr_singleton_refines hb hv1
              obtain ⟨hspabs2, hspwf⟩ := CoreK.append_exprs_refines htargs hv1wf hspine
              obtain ⟨r1, st2, hio, hok⟩ := bind_pair_eq_ok hok
              split at hok
              · rename_i b3
                obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
                  (iota_certs_i_refines hsc hw d false hptywf hspwf).apply hwf1 hfe hio
                    hrel1 hfrel
                rw [hspabs2, hv1abs] at hrun2
                rw [run_bind _ _ (by simpa using hrun2)]
                split at hok
                · rename_i hb3
                  obtain ⟨i3, hi3, hok⟩ := bind_eq_ok_iff.mp hok
                  have hi3v : i3.val = j.val + 1 := HashMap.uscalar_add_eq hi3
                  obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
                    ih (n_f.val - i3.val) (by omega) t us2 targs b lps_t n_f i3 ht hus2
                      htargs hb hlps rfl fe lfe hfe hfrel st2 r st' hwf2 hok lst2 hrel2
                  refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
                  rw [if_pos hb3, ← hi3v]
                  exact hrun3
                · rename_i hb3
                  have hb3f : b3 = false := by
                    simp only [Bool.not_eq_true] at hb3; exact hb3
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at hok
                  refine ⟨lst2, ?_, hok.2 ▸ hrel2, hok.2 ▸ hwf2, trivial⟩
                  rw [if_neg hb3, ← hok.1, hb3f]
                  rfl
              · rename_i err
                simp at hok
          · -- the telescope does not peel
            rename_i hsome
            have hstrip : ConLeche.Expr.stripPis ((absExprs targs).length + 1)
                (absExpr cvp.ty)
                = Option.map (fun p => (ExprOps.absBinders p.1, absExpr p.2)) o1 := by
              rw [htargslen, ← hi2v, ← hspabs]
            have hsomeL : ¬ ((absConstantVal cvp).type.stripPis
                ((absExprs targs).length + 1)).isSome = true := by
              simp only [absConstantVal, hstrip]
              cases o1 with
              | none => simp
              | some q => simp [core.option.Option.is_some] at hsome
            simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst, ?_, hrel, hwf, trivial⟩
            rw [if_neg (by rintro ⟨-, h2⟩; exact hsomeL h2)]
            rfl
        · -- the level parameters differ
          rename_i hb1f
          have hb1ff : b1 = false := by simpa using hb1f
          have hne : ¬ (absNames cvp.level_params = absNames lps_t) :=
            of_decide_eq_false (by rw [← hb1abs]; exact hb1ff)
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1)]
          rfl

/-- `ConLeche/Cached/CoreC.lean:388-405` — **`struct_eta_proj_certs_i_from`
refines `structEtaProjCertsI`** at the suffix the cursor names
(`core_c.rs:779`). -/
theorem struct_eta_proj_certs_i_from_refines (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) {t : name.Name}
    {us2 : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr} {b : expr.Expr}
    {lps_t : alloc.vec.Vec name.Name} (n_f j : Std.U64)
    (ht : NameWF t) (hus2 : LevelsWF us2) (htargs : ExprsWF targs) (hb : ExprWF b)
    (hlps : NamesWF lps_t) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_proj_certs_i_from mode fuel st fe d t us2
        targs b lps_t n_f j)
      (fun lfe => ConLeche.Cached.structEtaProjCertsI (knot mode lfe fuel.val) lfe d.val
        (absName t) (absName t) (absLevels us2) (absExprs targs) (absExpr b)
        (absNames lps_t) (List.range' j.val (n_f.val - j.val))) :=
  struct_eta_proj_certs_i_from_aux hsc hw d _ t us2 targs b lps_t n_f j ht hus2 htargs hb
    hlps rfl

/-- `ConLeche/Cached/CoreC.lean:388-405` — **`struct_eta_proj_certs_i` refines
`structEtaProjCertsI`** at the cited `List.range nF` (`core_c.rs:760`). -/
theorem struct_eta_proj_certs_i_refines (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) {t : name.Name}
    {us2 : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr} {b : expr.Expr}
    {lps_t : alloc.vec.Vec name.Name} (n_f : Std.U64)
    (ht : NameWF t) (hus2 : LevelsWF us2) (htargs : ExprsWF targs) (hb : ExprWF b)
    (hlps : NamesWF lps_t) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_proj_certs_i mode fuel st fe d t us2
        targs b lps_t n_f)
      (fun lfe => ConLeche.Cached.structEtaProjCertsI (knot mode lfe fuel.val) lfe d.val
        (absName t) (absName t) (absLevels us2) (absExprs targs) (absExpr b)
        (absNames lps_t) (List.range n_f.val)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.struct_eta_proj_certs_i at hok
  dsimp only at hok
  have := (struct_eta_proj_certs_i_from_refines hsc hw d n_f 0#u64 ht hus2 htargs hb
    hlps).apply hwf hfe hok hrel hfrel
  simpa [List.range_eq_range'] using this

/-! ## `struct_eta_cert_with_i` — the structure-eta certificate

`ConLeche/Cached/CoreC.lean:407-473 structEtaCertWithI` (`core_c.rs:839`).
The port hoists the cited definition's tail into two helpers
(`struct_eta_cert_steps_i` `:902`, `struct_eta_cert_fields_i` `:990`); the two
definitions below are those tails, written once, so that the hoisting is a
`rfl`-identity against the cited body and each helper gets a statement of its
own.  The cited `(Tn T : Name)` pair is one parameter in the port. -/

/-- `ConLeche/Cached/CoreC.lean:452-472` — the last two steps: the TT-lane
synthetic-spine certificate (task #137, `mode.ttChecks`, a literal `false` at
both shipped cores) and the field comparison against the fabricated
projections. -/
def structEtaCertFieldsI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (c : ConLeche.Name)
    (us us' : List ConLeche.Level) (aargs targs : List ConLeche.Cached.ExprC)
    (b : ConLeche.Cached.ExprC) (caps : ConLeche.IndCaps) (T : ConLeche.Name) :
    ConLeche.Cached.CheckCM Bool := do
  let projs ← ConLeche.Cached.projAppsI fe T T us' targs b caps.etaFields
  if ← (if mode.ttChecks then do
          let tyCtor ← ConLeche.Cached.constTyAtM fe c c us
          ConLeche.Cached.iotaCertsI r fe depth false tyCtor (targs ++ projs)
        else pure true) then
    ConLeche.Cached.defEqListI r fe depth (aargs.drop caps.etaParams) projs
  else pure false

/-- `ConLeche/Cached/CoreC.lean:431-472` — the state-touching steps in the
cited order: equivalent level lists, the type former's telescope certificate,
the per-slot ones, the parameter comparison, then the fields. -/
def structEtaCertStepsI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (c : ConLeche.Name)
    (us us' : List ConLeche.Level) (aargs targs : List ConLeche.Cached.ExprC)
    (b : ConLeche.Cached.ExprC) (cvT : ConLeche.ConstantVal) (caps : ConLeche.IndCaps)
    (T : ConLeche.Name) : ConLeche.Cached.CheckCM Bool := do
  if ← ConLeche.liftFueled "level comparison"
      (← ConLeche.Cached.isEquivListLM us us') then do
    let tyT ← ConLeche.Cached.constTyAtM fe T T us'
    if ← ConLeche.Cached.certAtI mode
        (ConLeche.Cached.iotaCertsI r fe depth false tyT targs) then do
      if ← ConLeche.Cached.certAtI mode
          (if fe.towerSlotsAllF T caps.etaFields then pure true
           else ConLeche.Cached.structEtaProjCertsI r fe depth T T us' targs b
             cvT.levelParams (List.range caps.etaFields)) then do
        if ← ConLeche.Cached.defEqListI r fe depth (aargs.take caps.etaParams) targs then
          structEtaCertFieldsI mode r fe depth c us us' aargs targs b caps T
        else pure false
      else pure false
    else pure false
  else pure false

/-- `ConLeche/Cached/CoreC.lean:452-472` — **`struct_eta_cert_fields_i` refines
the cited last two steps** (`core_c.rs:990`). -/
theorem struct_eta_cert_fields_i_refines (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) {c t : name.Name}
    {us us2 : alloc.vec.Vec level.Level} {aargs targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} {cvc : env.ConstantVal} {caps : env.IndCaps}
    (hc : NameWF c) (ht : NameWF t) (hus : LevelsWF us) (hus2 : LevelsWF us2)
    (haargs : ExprsWF aargs) (htargs : ExprsWF targs) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_fields_i mode fuel st fe d c us us2
        aargs targs b cvc caps t)
      (fun lfe => structEtaCertFieldsI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absName c) (absLevels us) (absLevels us2) (absExprs aargs) (absExprs targs)
        (absExpr b) (absIndCaps caps) (absName t)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.struct_eta_cert_fields_i at hok
  dsimp only at hok
  rw [structEtaCertFieldsI]
  simp only [absIndCaps]
  obtain ⟨projs, hprojs, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hpabs, hpwf⟩ := proj_apps_i_refines hfe hfrel ht hus2 htargs hb projs hprojs
  rw [← hpabs, run_bind _ _ (run_pure _ _)]
  obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
  have hb1abs : b1 = (absMode mode).ttChecks := Env.tt_checks_refines hb1
  obtain ⟨st1, tt, hbranch, hok⟩ := bind_pair_eq_ok hok
  rw [← hb1abs]
  -- the field comparison, shared by the two TT arms
  have tail : ∀ (st2 : cached.state_c.CState) (lst2 : ConLeche.Cached.CState) (b2 : Bool),
      StateWF st2 → StateRel st2 lst2 →
      ((if b2 = true then
          (do let fields ← kernel.core_k.drop_exprs_n aargs caps.eta_params
              cached.core_c.def_eq_list_i mode fuel st2 fe d fields projs)
        else ok (core.result.Result.Ok b2, st2)) = ok (core.result.Result.Ok r, st')) →
      ∃ lst', (if b2 = true then
            ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
              ((absExprs aargs).drop (absIndCaps caps).etaParams) (absExprs projs)
          else pure false).run lst2 = .ok (id r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ True := by
    intro st2 lst2 b2 hwf2 hrel2 htl
    split at htl
    · rename_i hb2
      rw [if_pos hb2]
      obtain ⟨fields, hfields, htl⟩ := bind_eq_ok_iff.mp htl
      obtain ⟨hfabs, hfwf⟩ := CoreK.drop_exprs_n_refines haargs hfields
      obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
        (def_eq_list_i_refines hw d hfwf hpwf).apply hwf2 hfe htl hrel2 hfrel
      refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
      rw [hfabs] at hrun3
      exact hrun3
    · rename_i hb2
      have hb2f : b2 = false := by simp only [Bool.not_eq_true] at hb2; exact hb2
      rw [if_neg hb2]
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at htl
      refine ⟨lst2, ?_, htl.2 ▸ hrel2, htl.2 ▸ hwf2, trivial⟩
      rw [← htl.1, hb2f]
      rfl
  split at hbranch
  · -- the TT-lane arm (dead at both shipped cores, but ported)
    rename_i hb1t
    rw [if_pos hb1t]
    simp only [bind_assoc]
    obtain ⟨rr, st2, hcty, hbranch⟩ := bind_pair_eq_ok hbranch
    cases rr with
    | Err err =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hbranch
      obtain ⟨rfl, rfl⟩ := hbranch
      simp at hok
    | Ok cty =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hctywf⟩ :=
        StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hc hus hcty
          lst lfe hrel hfrel (absName c)
      rw [run_bind _ _ hrun2]
      obtain ⟨v, hv, hbranch⟩ := bind_eq_ok_iff.mp hbranch
      have hvv : v = targs := Env.exprs_copy_refines hv
      rw [hvv] at hbranch
      obtain ⟨spine, hspine, hbranch⟩ := bind_eq_ok_iff.mp hbranch
      obtain ⟨hspabs, hspwf⟩ := CoreK.append_exprs_refines htargs hpwf hspine
      obtain ⟨tt1, st3, hio, hbranch⟩ := bind_pair_eq_ok hbranch
      simp only [Result.ok.injEq, Prod.mk.injEq] at hbranch
      obtain ⟨hst1, htt⟩ := hbranch
      rw [← hst1, ← htt] at hok
      split at hok
      · rename_i b2
        obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
          (iota_certs_i_refines hsc hw d false hctywf hspwf).apply hwf2 hfe hio hrel2 hfrel
        rw [hspabs] at hrun3
        rw [run_bind _ _ (by simpa using hrun3)]
        exact tail _ _ b2 hwf3 hrel3 hok
      · rename_i err
        simp at hok
  · -- the TT lane is off: the certificate is `true` without running
    rename_i hb1f
    rw [if_neg hb1f]
    simp only [Result.ok.injEq, Prod.mk.injEq] at hbranch
    obtain ⟨rfl, rfl⟩ := hbranch
    rw [run_bind _ _ (run_pure _ _)]
    exact tail _ _ true hwf hrel hok

/-- `ConLeche/Cached/CoreC.lean:431-472` — **`struct_eta_cert_steps_i` refines
the cited state-touching steps** (`core_c.rs:902`).  The type former's type is
read *before* the `certAtI` gate on both sides, so the `.trusted` arm threads
the `constTyAtM` memo through too (task #61).  Every peeled hypothesis gets a
name of its own: a reused one is *shadowed*, not cleared, and a later `cases`
hands the name back to the shadowed hypothesis. -/
theorem struct_eta_cert_steps_i_refines (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) {c t : name.Name}
    {us us2 : alloc.vec.Vec level.Level} {aargs targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} {cvc cvt : env.ConstantVal} {caps : env.IndCaps}
    (hc : NameWF c) (ht : NameWF t) (hus : LevelsWF us) (hus2 : LevelsWF us2)
    (haargs : ExprsWF aargs) (htargs : ExprsWF targs) (hb : ExprWF b)
    (hcvt : ConstantValWF cvt) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_steps_i mode fuel st fe d c us us2
        aargs targs b cvc cvt caps t)
      (fun lfe => structEtaCertStepsI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absName c) (absLevels us) (absLevels us2) (absExprs aargs) (absExprs targs)
        (absExpr b) (absConstantVal cvt) (absIndCaps caps) (absName t)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.struct_eta_cert_steps_i at hok
  dsimp only at hok
  rw [structEtaCertStepsI]
  simp only [absIndCaps, absConstantVal]
  -- the level lists
  obtain ⟨eqv, st1, heqv, hA⟩ := bind_pair_eq_ok hok
  obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
    StateC.is_equiv_list_l_m_refines hwf hus hus2 heqv lst hrel
  obtain ⟨rq, hlift, hB⟩ := bind_eq_ok_iff.mp hA
  cases rq with
  | Err err => simp at hB
  | Ok b1 =>
    have heqvsome : eqv = some b1 := lift_fueled_some hlift
    rw [run_bind _ _ hrun1, run_bind _ _ (run_liftFueled _ _ heqvsome)]
    dsimp only at hB
    split at hB
    · -- the level lists agree
      rename_i hb1t
      subst hb1t
      rw [if_pos rfl]
      -- the type former's type, read *before* the gate
      obtain ⟨r1, st2, hcty, hC⟩ := bind_pair_eq_ok hB
      cases r1 with
      | Err err => simp at hC
      | Ok tty =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, htywf⟩ :=
          StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf1 hfe ht hus2 hcty
            lst1 lfe hrel1 hfrel (absName t)
        rw [run_bind _ _ hrun2]
        obtain ⟨st3, tele, htele, hD⟩ := bind_pair_eq_ok hC
        -- the telescope certificate: a certificate family, so `certAtI`-gated
        have hgate : ∀ b2 : Bool, tele = core.result.Result.Ok b2 →
            ∃ lst3, StateRel st3 lst3 ∧ StateWF st3 ∧
              ∀ f : Bool → ConLeche.Cached.CheckCM Bool,
                (ConLeche.Cached.certAtI (absMode mode)
                    (ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val false
                      (absExpr tty) (absExprs targs)) >>= f).run lst2
                      = (f b2).run lst3 := by
          intro b2 hb2
          obtain ⟨cg, hcg, htl⟩ := bind_eq_ok_iff.mp htele
          have hcgabs : cg = (absMode mode).certs := Env.certs_refines hcg
          split at htl
          · -- the family runs
            rename_i hcgt
            have hcerts : (absMode mode).certs = true := by rw [← hcgabs]; exact hcgt
            obtain ⟨tele1, st4, hio, htl2⟩ := bind_pair_eq_ok htl
            simp only [Result.ok.injEq, Prod.mk.injEq] at htl2
            obtain ⟨hst, hte⟩ := htl2
            rw [hst, hte, hb2] at hio
            obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
              (iota_certs_i_refines hsc hw d false htywf htargs).apply hwf2 hfe hio hrel2
                hfrel
            refine ⟨lst3, hrel3, hwf3, fun f => ?_⟩
            rw [ConLeche.Cached.certAtI, if_pos hcerts]
            exact run_bind _ _ (by simpa using hrun3)
          · -- the family is off: `true` without running, on the moved state
            rename_i hcgf
            have hcerts : ¬ ((absMode mode).certs = true) := by rw [← hcgabs]; exact hcgf
            simp only [Result.ok.injEq, Prod.mk.injEq] at htl
            obtain ⟨hst, hte⟩ := htl
            have hb2t : b2 = true := by simpa using (hte.trans hb2).symm
            refine ⟨lst2, hst ▸ hrel2, hst ▸ hwf2, fun f => ?_⟩
            rw [ConLeche.Cached.certAtI, if_neg hcerts, hb2t]
            exact run_bind _ _ (run_pure _ _)
        cases tele with
        | Err err => simp at hD
        | Ok b2 =>
          obtain ⟨lst3, hrel3, hwf3, hrun3⟩ := hgate b2 rfl
          rw [hrun3]
          dsimp only at hD
          split at hD
          · -- the telescope is certified
            rename_i hb2t
            subst hb2t
            rw [if_pos rfl]
            -- the per-slot certificates: a certificate family too
            obtain ⟨cg2, hcg2, hE⟩ := bind_eq_ok_iff.mp hD
            have hcg2abs : cg2 = (absMode mode).certs := Env.certs_refines hcg2
            obtain ⟨st4, cs, hslots, hF⟩ := bind_pair_eq_ok hE
            obtain ⟨caps1, slots⟩ := cs
            -- the destructuring `let` the triple leaves behind (see
            -- `bind_pair_eq_ok`): this `replace` is the iota step
            replace hF : (match slots with
                | core.result.Result.Ok b4 =>
                  if b4 = true then
                    (do let params ← kernel.core_k.take_exprs_n aargs caps1.eta_params
                        let (r2, st5) ← cached.core_c.def_eq_list_i mode fuel st4 fe d
                          params targs
                        match r2 with
                        | core.result.Result.Ok b5 =>
                          if b5 = true then
                            cached.core_c.struct_eta_cert_fields_i mode fuel st5 fe d c
                              us us2 aargs targs b cvc caps1 t
                          else ok (r2, st5)
                        | core.result.Result.Err _ => ok (r2, st5))
                  else ok (slots, st4)
                | core.result.Result.Err _ => ok (slots, st4))
                = ok (core.result.Result.Ok r, st') := hF
            have hgate2 : ∀ b3 : Bool, slots = core.result.Result.Ok b3 →
                caps1 = caps ∧ ∃ lst4, StateRel st4 lst4 ∧ StateWF st4 ∧
                  ∀ f : Bool → ConLeche.Cached.CheckCM Bool,
                    (ConLeche.Cached.certAtI (absMode mode)
                        (if lfe.towerSlotsAllF (absName t) caps.eta_fields.val
                         then pure true
                         else ConLeche.Cached.structEtaProjCertsI (knot mode lfe fuel.val)
                           lfe d.val (absName t) (absName t) (absLevels us2)
                           (absExprs targs) (absExpr b) (absNames cvt.level_params)
                           (List.range caps.eta_fields.val)) >>= f).run lst3
                      = (f b3).run lst4 := by
              intro b3 hb3
              split at hslots
              · -- the family runs
                rename_i hcg2t
                have hcerts : (absMode mode).certs = true := by
                  rw [← hcg2abs]; exact hcg2t
                obtain ⟨tw, htw, hsl1⟩ := bind_eq_ok_iff.mp hslots
                have htwabs : tw = lfe.towerSlotsAllF (absName t) caps.eta_fields.val :=
                  ConRon.Refine.tower_slots_all_f_refines (FindAgree.of_rel hfrel hfe)
                    (FindWF.of_wf hfe) ht htw
                obtain ⟨c1, r2, hinner, hsl2⟩ := bind_pair_eq_ok hsl1
                simp only [Result.ok.injEq, Prod.mk.injEq] at hsl2
                obtain ⟨hc1, hcaps, hr2⟩ := hsl2
                refine ⟨hcaps.symm, ?_⟩
                split at hinner
                · -- an all-tower slot family has no per-slot certificates
                  rename_i htwt
                  simp only [Result.ok.injEq, Prod.mk.injEq] at hinner
                  obtain ⟨hc1', hr2'⟩ := hinner
                  have hb3t : b3 = true := by
                    simpa using ((hr2'.trans hr2).trans hb3).symm
                  refine ⟨lst3, ?_, ?_, fun f => ?_⟩
                  · rw [← hc1, ← hc1']; exact hrel3
                  · rw [← hc1, ← hc1']; exact hwf3
                  · rw [ConLeche.Cached.certAtI, if_pos hcerts, ← htwabs, if_pos htwt,
                      hb3t]
                    exact run_bind _ _ (run_pure _ _)
                · -- the projection-function slots are certified one by one
                  rename_i htwf
                  obtain ⟨slots1, st5, hsp, hin2⟩ := bind_pair_eq_ok hinner
                  simp only [Result.ok.injEq, Prod.mk.injEq] at hin2
                  obtain ⟨hst5, hsl⟩ := hin2
                  rw [hst5, hc1, hsl, hr2, hb3] at hsp
                  obtain ⟨lst4, hrun4, hrel4, hwf4, -⟩ :=
                    (struct_eta_proj_certs_i_refines hsc hw d caps.eta_fields ht hus2
                      htargs hb hcvt.2.1).apply hwf3 hfe hsp hrel3 hfrel
                  refine ⟨lst4, hrel4, hwf4, fun f => ?_⟩
                  rw [ConLeche.Cached.certAtI, if_pos hcerts, ← htwabs, if_neg htwf]
                  exact run_bind _ _ (by simpa using hrun4)
              · -- the family is off: `true` without running
                rename_i hcg2f
                have hcerts : ¬ ((absMode mode).certs = true) := by
                  rw [← hcg2abs]; exact hcg2f
                simp only [Result.ok.injEq, Prod.mk.injEq] at hslots
                obtain ⟨hst4, hcaps, hsl⟩ := hslots
                have hb3t : b3 = true := by simpa using (hsl.trans hb3).symm
                refine ⟨hcaps.symm, lst3, hst4 ▸ hrel3, hst4 ▸ hwf3, fun f => ?_⟩
                rw [ConLeche.Cached.certAtI, if_neg hcerts, hb3t]
                exact run_bind _ _ (run_pure _ _)
            cases slots with
            | Err err => simp at hF
            | Ok b3 =>
              obtain ⟨hcaps, lst4, hrel4, hwf4, hrun4⟩ := hgate2 b3 rfl
              subst hcaps
              rw [hrun4]
              dsimp only at hF
              split at hF
              · -- the slots are certified: the parameter comparison
                rename_i hb3t
                subst hb3t
                rw [if_pos rfl]
                obtain ⟨params, hparams, hG⟩ := bind_eq_ok_iff.mp hF
                obtain ⟨hpabs, hpwf⟩ := CoreK.take_exprs_n_refines haargs hparams
                obtain ⟨r2, st5, hdq, hH⟩ := bind_pair_eq_ok hG
                cases r2 with
                | Err err => simp at hH
                | Ok b4 =>
                  obtain ⟨lst5, hrun5, hrel5, hwf5, -⟩ :=
                    (def_eq_list_i_refines hw d hpwf htargs).apply hwf4 hfe hdq hrel4
                      hfrel
                  rw [hpabs] at hrun5
                  rw [run_bind _ _ (by simpa using hrun5)]
                  dsimp only at hH
                  split at hH
                  · -- the parameters agree: on to the fields
                    rename_i hb4t
                    subst hb4t
                    rw [if_pos rfl]
                    exact (struct_eta_cert_fields_i_refines hsc hw d hc ht hus hus2 haargs
                      htargs hb).apply hwf5 hfe hH hrel5 hfrel
                  · -- the parameters differ
                    rename_i hb4f
                    have hb4ff : b4 = false := by simpa using hb4f
                    subst hb4ff
                    simp only [Result.ok.injEq, Prod.mk.injEq,
                      core.result.Result.Ok.injEq] at hH
                    obtain ⟨rfl, rfl⟩ := hH
                    refine ⟨lst5, ?_, hrel5, hwf5, trivial⟩
                    rw [if_neg (by simp)]
                    rfl
              · -- a slot certificate failed
                rename_i hb3f
                have hb3ff : b3 = false := by simpa using hb3f
                subst hb3ff
                simp only [Result.ok.injEq, Prod.mk.injEq,
                  core.result.Result.Ok.injEq] at hF
                obtain ⟨rfl, rfl⟩ := hF
                refine ⟨lst4, ?_, hrel4, hwf4, trivial⟩
                rw [if_neg (by simp)]
                rfl
          · -- the telescope certificate failed
            rename_i hb2f
            have hb2ff : b2 = false := by simpa using hb2f
            subst hb2ff
            simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hD
            obtain ⟨rfl, rfl⟩ := hD
            refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
            rw [if_neg (by simp)]
            rfl
    · -- the level lists differ
      rename_i hb1f
      have hb1ff : b1 = false := by simpa using hb1f
      subst hb1ff
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      refine ⟨lst1, ?_, hrel1, hwf1, trivial⟩
      rw [if_neg (by simp)]
      rfl

/-- `ConLeche/Cached/CoreC.lean:407-473` — **`struct_eta_cert_with_i` refines
`structEtaCertWithI`** (`core_c.rs:839`): the structure-eta certificate against
a given weak-head-normal type of the stuck side. -/
theorem struct_eta_cert_with_i_refines (hsc : StateCOpen) {mode : env.CheckMode}
    {fuel : Std.U64} (hw : Wrappers mode fuel) (d : Std.U64) {a b wtb : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) (hwtb : ExprWF wtb) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_with_i mode fuel st fe d a b wtb)
      (fun lfe => ConLeche.Cached.structEtaCertWithI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b) (absExpr wtb)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  dsimp only
  unfold cached.core_c.struct_eta_cert_with_i at hok
  dsimp only at hok
  rw [ConLeche.Cached.structEtaCertWithI]
  obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hfaabs, hfawf⟩ := ExprOps.get_app_fn_refines ha hfa
  rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hfaabs, CoreK.absExpr_kind fa]
  simp only [arc_deref_eq, bind_tc_ok] at hok
  split at hok
  case h_4 c us hk =>
    -- the head is a constant
    obtain ⟨hcwf, huswf⟩ := CoreK.ExprWF.const_children hfawf hk
    rw [hk]
    simp only [absExprKind]
    rw [run_bind _ _ (run_pure _ _)]
    obtain ⟨o, hprobe, hok⟩ := bind_eq_ok_iff.mp hok
    cases o with
    | none =>
      have hmiss := CoreK.ctor_probe_miss CoreK.envFacts (FindAgree.of_rel hfrel hfe)
        (FindWF.of_wf hfe) hcwf hprobe
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine ⟨lst, ?_, hrel, hwf, trivial⟩
      cases hf : lfe.find? (absName c) with
      | none => simp
      | some ci =>
        cases ci with
        | ctorInfo cv p f => exact absurd hf (hmiss cv p f)
        | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | recInfo _ _ _ _
        | projInfo _ => simp
    | some p =>
      obtain ⟨cvc, cn_p, cn_f⟩ := p
      obtain ⟨hfind, hcvcwf⟩ := CoreK.ctor_probe_hit CoreK.envFacts
        (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hcwf hprobe
      rw [hfind]
      simp only
      obtain ⟨aargs, haa, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨haaabs, haawf⟩ := ExprOps.get_app_args_refines ha haa
      rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← haaabs]
      rw [run_bind _ _ (run_pure _ _)]
      obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
      have hi1v : i1.val = aargs.val.length := by
        have := ExprOps.usize_cast_u64_val (alloc.vec.Vec.len aargs)
        have := alloc.vec.Vec.len_val aargs
        simp only [lift_eq, Result.ok.injEq] at hi1
        scalar_tac
      have hi2v : i2.val = cn_p.val + cn_f.val := HashMap.uscalar_add_eq hi2
      have haalen : (absExprs aargs).length = aargs.val.length := by simp [absExprs]
      split at hok
      · -- the arity does not fit
        rename_i hne
        have hneL : ¬ ((absExprs aargs).length = cn_p.val + cn_f.val) := by
          rw [haalen, ← hi1v, ← hi2v]
          intro hc
          exact absurd (Std.UScalar.val_eq_imp_iff.mpr hc) (by simpa using hne)
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, trivial⟩
        rw [if_neg hneL]
        rfl
      · -- the arity fits
        rename_i heq
        have heqL : (absExprs aargs).length = cn_p.val + cn_f.val := by
          rw [haalen, ← hi1v, ← hi2v]
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
          rw [heq]
        rw [if_pos heqL]
        obtain ⟨ftb, hftb, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hftbabs, hftbwf⟩ := ExprOps.get_app_fn_refines hwtb hftb
        rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hftbabs, CoreK.absExpr_kind ftb]
        split at hok
        case h_4 t us2 hk2 =>
          obtain ⟨htwf, hus2wf⟩ := CoreK.ExprWF.const_children hftbwf hk2
          rw [hk2]
          simp only [absExprKind]
          rw [run_bind _ _ (run_pure _ _)]
          obtain ⟨o1, hprobe2, hok⟩ := bind_eq_ok_iff.mp hok
          cases o1 with
          | none =>
            have hmiss := CoreK.ind_probe_miss CoreK.envFacts (FindAgree.of_rel hfrel hfe)
              (FindWF.of_wf hfe) htwf hprobe2
            simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst, ?_, hrel, hwf, trivial⟩
            cases hf : lfe.find? (absName t) with
            | none => simp
            | some ci =>
              cases ci with
              | indInfo cv cp => exact absurd hf (hmiss cv cp)
              | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _
              | recInfo _ _ _ _ | projInfo _ => simp
          | some q =>
            obtain ⟨cvt, caps⟩ := q
            obtain ⟨hfind2, hcvtwf, hcapswf⟩ := CoreK.ind_probe_hit CoreK.envFacts
              (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) htwf hprobe2
            rw [hfind2]
            simp only
            obtain ⟨targs, hta, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨htaabs, htawf⟩ := ExprOps.get_app_args_refines hwtb hta
            rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← htaabs]
            rw [run_bind _ _ (run_pure _ _)]
            obtain ⟨b1, hshape, hok⟩ := bind_eq_ok_iff.mp hok
            have hshapeabs := CoreK.struct_eta_shape_ok_refines
              CoreK.pinned_reserved_basis_names (FindAgree.of_rel hfrel hfe)
              (FindWF.of_wf hfe) hcwf htwf hcvcwf hcvtwf hcapswf hshape
            split at hok
            · -- the syntactic block holds: the state-touching steps
              rename_i hb1t
              have hshapeconj := of_decide_eq_true (show decide _ = true by
                rw [← hshapeabs]; exact hb1t)
              rw [if_pos hshapeconj]
              exact (struct_eta_cert_steps_i_refines hsc hw d hcwf htwf huswf hus2wf
                haawf htawf hb hcvtwf).apply hwf hfe hok hrel hfrel
            · -- the syntactic block fails
              rename_i hb1f
              have hb1ff : b1 = false := by
                simp only [Bool.not_eq_true] at hb1f; exact hb1f
              simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst, ?_, hrel, hwf, trivial⟩
              rw [if_neg (of_decide_eq_false (by rw [← hshapeabs]; exact hb1ff))]
              rfl
        all_goals (rename_i hk2
                   simp only [Result.ok.injEq, Prod.mk.injEq,
                     core.result.Result.Ok.injEq] at hok
                   obtain ⟨rfl, rfl⟩ := hok
                   refine ⟨lst, ?_, hrel, hwf, trivial⟩
                   rw [hk2]; simp)
  all_goals (rename_i hk
             simp only [Result.ok.injEq, Prod.mk.injEq,
               core.result.Result.Ok.injEq] at hok
             obtain ⟨rfl, rfl⟩ := hok
             refine ⟨lst, ?_, hrel, hwf, trivial⟩
             rw [hk]; simp)
end ConRon.Refine.Core

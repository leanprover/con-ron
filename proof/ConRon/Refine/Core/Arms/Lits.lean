/-
# The literal-reduction arm of the knot (task #55)

The group `whnf` and `defeq` share for the δ step's materialisation and for
`Nat`-literal acceleration: `unfoldDefinitionI` (with its owning probe
`defn_lp_count`) and `reduceNatI` (with the two factorings `reduce_nat_bin_i`
and `reduce_nat_lits_i` the port introduces and con-leche writes inline).

Every state-free ingredient is task #49's (`Refine/CoreKLits.lean`,
`Refine/CoreKNames.lean`, `Refine/CoreKSupport.lean`,
`Refine/CoreKNatOps.lean`) and every cached one task #51/#52's
(`Refine/ExprOpsC.lean`, `Refine/StateC.lean`).  Nothing new is assumed except
the pins, which `Refine/CoreKPinned.lean` discharges unconditionally.

**Task #61 retired the group's one `sorry`.**  `core_k::nat_op_result` used to
answer `none` on a `Nat.shiftLeft`/`Nat.shiftRight` amount that does not fit a
`u64`, where the cited `natOpResult` computes a literal; `none` is a different
verdict, so `reduce_nat_bin_i`'s exact-result claim was false in that one spot.
The port now *fails* there instead, which §3.5 leaves unconstrained, so
`Refine/CoreKLits.lean`'s `OpSpec` is exact in both directions and the arm goes
through.  What the arm gained is one `core::result::Result` layer to
destructure, and the census at the foot of the file records that nothing here
is owed.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.Core.Arms.Bridge
import ConRon.Refine.CoreKLits
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsSpine

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The monad plumbing, again

`Shape.lean`'s set is `local`, so it does not cross the file boundary; these
are the same attributes, re-declared. -/

attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-! ## `defn_lp_count` — the owning probe of `unfoldDefinitionI`'s guard -/

/-- `ConLeche/Cached/CoreC.lean:69` — **`defn_lp_count` refines the cited
`match fe.find? nm with | some (.defnInfo cv _ _) => …` destructuring**, at the
one field the guard reads: the level-parameter count (`core_c.rs:160`). -/
theorem defn_lp_count_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} (hfe : FEnvRel fe lfe) (hfwf : FEnvWF fe) (hn : NameWF n) :
    SimP (Option.map (fun i : Std.Usize => i.val)) (fun _ => True)
      (cached.core_c.defn_lp_count fe n)
      (match lfe.find? (absName n) with
        | some (.defnInfo cv _ _) => some cv.levelParams.length
        | _ => none) := by
  intro r h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.defn_lp_count] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  have habs := FEnv.find_refines hfe hfwf hn ho
  cases o with
  | none =>
    simp only [Option.map_none] at habs
    rw [← habs]
    simp only [Result.ok.injEq] at h
    rw [← h]
    rfl
  | some ci =>
    simp only [Option.map_some] at habs
    rw [← habs]
    cases ci <;>
      first
        | (simp only [Result.ok.injEq] at h; rw [← h]; rfl)
        | skip
    rename_i cv v hint
    simp only [Result.ok.injEq] at h
    rw [← h]
    show some (alloc.vec.Vec.len cv.level_params).val
      = some (absNames cv.level_params).length
    simp [absNames]

/-! ## `unfold_definition_i` — the δ step's materialisation

`const_val_at_m`'s refinement (`Refine/StateC.lean`) runs under the named
ingredient `InstLevelParamsRefines`, which `Arms/Bridge.lean` discharges. -/

/-- `ConLeche/Cached/CoreC.lean:69` — **`unfold_definition_i` refines
`unfoldDefinitionI`** (`core_c.rs:180`): the δ step's materialisation, with the
unfolded value read through the `(name, levels)` cache. -/
theorem unfold_definition_i_refines {e : expr.Expr} (he : ExprWF e) :
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.unfold_definition_i st fe e)
      (fun lfe => ConLeche.Cached.unfoldDefinitionI lfe (absExpr e)) := by
  intro fe lfe hfwf hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.unfold_definition_i at hok
  simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at hok
  obtain ⟨f, hf, hok⟩ := hok
  obtain ⟨hfabs, hfwf'⟩ := ExprOps.get_app_fn_refines he hf
  have hkey : ConLeche.Cached.ExprC.getAppFn (absExpr e) = absExprKind f._0.kind := by
    rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hfabs, CoreK.absExpr_kind]
  simp only [ConLeche.Cached.unfoldDefinitionI, hkey]
  cases hk : f._0.kind
  all_goals rw [hk] at hok
  case Const n us1 =>
    obtain ⟨hnwf, huswf⟩ := CoreK.ExprWF.const_children hfwf' hk
    simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at hok
    obtain ⟨us2, hus2, hok⟩ := hok
    rw [Env.levels_copy_refines hus2] at hok
    obtain ⟨o, ho, hok⟩ := hok
    obtain ⟨hoabs, -⟩ := defn_lp_count_refines hfrel hfwf hnwf o ho
    simp only [absExprKind]
    cases hfind : lfe.find? (absName n) with
    | none =>
      rw [hfind] at hoabs
      have ho' : o = none := by cases o <;> simp_all
      subst ho'
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact ⟨lst, by simp [hfind], hrel, hwf, by simp⟩
    | some ci =>
      rw [hfind] at hoabs
      cases ci with
      | defnInfo cv value hint =>
        cases o with
        | none => simp at hoabs
        | some k =>
          simp only [Option.map_some, Option.some.injEq] at hoabs
          dsimp only at hok
          have hiff : (alloc.vec.Vec.len us1 = k)
              ↔ ((absLevels us1).length = cv.levelParams.length) := by
            rw [← hoabs]
            simp only [absLevels, List.length_map]
            constructor
            · intro h; scalar_tac
            · intro h; scalar_tac
          by_cases hlen : alloc.vec.Vec.len us1 = k
          · rw [if_pos hlen] at hok
            obtain ⟨p, hcv, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨rr, st1⟩ := p
            cases rr with
            | Err err =>
              replace hok : (ok (core.result.Result.Err err, st1)
                : Result ((core.result.Result (Option expr.Expr) core_types.CheckError)
                  × state_c.CState)) = ok (.Ok r, st') := hok
              simp at hok
            | Ok v1 =>
              replace hok : (do
                  let args ← expr_ops.get_app_args e
                  let e1 ← state_c.mk_app_n_m v1 args
                  ok (core.result.Result.Ok (some e1), st1))
                = ok (core.result.Result.Ok r, st') := hok
              simp only [bind_eq_ok_iff] at hok
              obtain ⟨args, hargs, e1, he1, hok⟩ := hok
              obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines he hargs
              rw [StateC.mk_app_n_m_eq] at he1
              obtain ⟨lst1, hrun, hrel1, hwf1, hv1wf⟩ :=
                StateC.const_val_at_m_refines instLevelParamsRefines hwf hfwf hnwf huswf hcv
                  lst lfe hrel hfrel (absName n)
              obtain ⟨he1abs, he1wf⟩ := ExprOpsC.mk_app_n_refines hv1wf hargswf he1
              simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst1, ?_, hrel1, hwf1, ?_⟩
              · have hrun' :
                    ConLeche.Cached.constValAtM lfe (absName n) (absName n) (absLevels us1) lst
                      = Except.ok (absExpr v1, lst1) := hrun
                simp only [StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure,
                  Except.bind, Except.pure, ConLeche.Cached.mkAppNM, hfind,
                  if_pos (hiff.mp hlen), hrun']
                rw [Option.map_some, he1abs, ConLeche.Cached.ExprC.getAppArgs_spec,
                  ← hargsabs]
              · intro x hx
                simp only [Option.some.injEq] at hx
                exact hx ▸ he1wf
          · rw [if_neg hlen] at hok
            simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact ⟨lst, by simp [hfind, if_neg (fun h => hlen (hiff.mpr h))], hrel, hwf, by simp⟩
      | _ =>
        have ho' : o = none := by cases o <;> simp_all
        subst ho'
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ⟨lst, by simp [hfind], hrel, hwf, by simp⟩
  all_goals
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact ⟨lst, by simp, hrel, hwf, by simp⟩

/-- **The one bind shape the block is made of**: a Rust call that threads the
state and answers a `core::result::Result`, followed by the `match` that
propagates its error.  Applied to the `ok` hypothesis the *unifier* sees
through the pattern-`let` Aeneas emits for the pair (`Refine/FEnv.lean`'s
note), which is what makes one lemma serve every call site below. -/
private theorem bindP {α β γ : Type} {f : Result (α × β)} {g : α × β → Result γ} {c : γ}
    (h : (f >>= g) = ok c) : ∃ x y, f = ok (x, y) ∧ g (x, y) = ok c := by
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x, y⟩ := p
  exact ⟨x, y, hp, h⟩

/-- **One con-leche bind, run**: the `run` of `x >>= g` at a state where `x`'s
own `run` is known.  The only monad plumbing the group needs. -/
private theorem runBind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {g : α → ConLeche.Cached.CheckCM β} {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : x.run lst = .ok (a, lst')) : (x >>= g).run lst = (g a).run lst' := by
  have h' : x lst = Except.ok (a, lst') := h
  simp only [StateT.run, StateT.bind, Bind.bind, Except.bind, h']

/-- The `run` of a con-leche `pure`. -/
private theorem runPure {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl

/-- `Cached/StateC.lean:99-103` — `rawNatLitC?` *is* `rawNatLit?`
(`ExprC = Expr`), which is the form `Refine/CoreKLits.lean` states. -/
private theorem rawNatLitC_eq (e : ConLeche.Expr) :
    ConLeche.Cached.rawNatLitC? e = ConLeche.rawNatLit? e := by
  cases e with
  | lit l => cases l <;> rfl
  | const c us =>
    cases us with
    | nil => simp only [ConLeche.Cached.rawNatLitC?, ConLeche.rawNatLit?, beq_iff_eq]
    | cons => rfl
  | _ => rfl

/-! ## `reduceNatI`'s inlined fragments

`ConLeche/Cached/CoreC.lean:92-152` writes the two-literal read and the
certified fold inline, once per arm, where `core_c.rs` factors them out
(`reduce_nat_lits_i`, `reduce_nat_bin_i`).  These two definitions *are* those
fragments, named so that the two factored functions have a statement of their
own; what pins them is `reduce_nat_i_refines`, which is stated against the
cited `reduceNatI` itself. -/

/-- `CoreC.lean:126-133` / `:140-147` — the two-literal read both binary arms
share: head-normalise the first argument and stop unless it is a literal, then
the second. -/
def natLitsI (r : ConLeche.Cached.CoreFnsI) (depth : Nat) (a b : ConLeche.Expr) :
    ConLeche.Cached.CheckCM (Option (Nat × Nat)) := do
  let w₁ ← r.whnf depth a
  match ConLeche.Cached.rawNatLitC? w₁ with
  | some n₁ => do
    let w₂ ← r.whnf depth b
    match ConLeche.Cached.rawNatLitC? w₂ with
    | some n₂ => pure (some (n₁, n₂))
    | none => pure none
  | none => pure none

/-- `CoreC.lean:126-137` — the certified-operation arm of the cited body,
verbatim: the two-literal read interleaved with `natOpResult`'s fold. -/
def natBinI (r : ConLeche.Cached.CoreFnsI) (depth : Nat) (c : ConLeche.Name)
    (a b : ConLeche.Expr) : ConLeche.Cached.CheckCM (Option ConLeche.Expr) := do
  let w₁ ← r.whnf depth a
  match ← pure (ConLeche.Cached.rawNatLitC? w₁) with
  | some n₁ => do
    let w₂ ← r.whnf depth b
    match ← pure (ConLeche.Cached.rawNatLitC? w₂) with
    | some n₂ =>
      match ConLeche.natOpResult c n₁ n₂ with
      | some x => do
        let r ← pure x
        pure (some r)
      | none => pure none
    | none => pure none
  | none => pure none

/-- **The two-literal read, replayed once for every arm that makes it.**
`reduce_nat_lits_i` is the port's factoring of a fragment con-leche writes
inline three times, each time under a different continuation; this is that
fragment's refinement, quantified over the continuation, so that the three
arms below each instantiate it and nothing is proved twice.

The two `whnf` calls are the wrappers (`hw.whnfSim`), the two literal reads
task #49's `raw_nat_lit_refines`. -/
private theorem lits_replay {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfwf : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    {st st1 : cached.state_c.CState} {o : Option (ron.nat.Nat × ron.nat.Nat)}
    (hwf : StateWF st)
    (h : cached.core_c.reduce_nat_lits_i mode fuel st fe d a b = ok (.Ok o, st1))
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) :
    ∃ lst1, StateRel st1 lst1 ∧ StateWF st1
      ∧ (∀ p, o = some p → Nat.NatWF p.1 ∧ Nat.NatWF p.2)
      ∧ ∀ {β : Type} (g : Option (Nat × Nat) → ConLeche.Cached.CheckCM β),
          (do
            let w₁ ← (knot mode lfe fuel.val).whnf d.val (absExpr a)
            match ← pure (ConLeche.Cached.rawNatLitC? w₁) with
            | some n₁ => do
              let w₂ ← (knot mode lfe fuel.val).whnf d.val (absExpr b)
              match ← pure (ConLeche.Cached.rawNatLitC? w₂) with
              | some n₂ => g (some (n₁, n₂))
              | none => g none
            | none => g none).run lst
            = (g (o.map (fun p => (Nat.toNat p.1, Nat.toNat p.2)))).run lst1 := by
  unfold cached.core_c.reduce_nat_lits_i at h
  obtain ⟨rr, s1, hw1, h⟩ := bindP h
  cases rr with
  | Err err => have := Result.ok_injective h; simp at this
  | Ok wa =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hwawf⟩ := (hw.whnfSim d ha).apply hwf hfwf hw1 hrel hfrel
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := CoreK.raw_nat_lit_refines hwawf CoreK.pinned_nat_zero_name ho1
    cases o1 with
    | none =>
      have h2 := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨lst1, hrel1, hwf1, by simp, ?_⟩
      intro β g
      rw [runBind hrun1, runBind (runPure _ lst1), rawNatLitC_eq, ← ho1abs]
      rfl
    | some n1 =>
      obtain ⟨rr2, s2, hw2, h⟩ := bindP h
      cases rr2 with
      | Err err => have := Result.ok_injective h; simp at this
      | Ok wb =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, hwbwf⟩ :=
          (hw.whnfSim d hb).apply hwf1 hfwf hw2 hrel1 hfrel
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ho2abs, ho2wf⟩ := CoreK.raw_nat_lit_refines hwbwf CoreK.pinned_nat_zero_name ho2
        cases o2 with
        | none =>
          have h2 := Result.ok_injective h
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨lst2, hrel2, hwf2, by simp, ?_⟩
          intro β g
          rw [runBind hrun1, runBind (runPure _ lst1), rawNatLitC_eq, ← ho1abs]
          simp only [Option.map_some]
          rw [runBind hrun2, runBind (runPure _ lst2), rawNatLitC_eq, ← ho2abs]
          rfl
        | some n2 =>
          have h2 := Result.ok_injective h
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨lst2, hrel2, hwf2, ?_, ?_⟩
          · intro p hp
            simp only [Option.some.injEq] at hp
            exact hp ▸ ⟨ho1wf n1 rfl, ho2wf n2 rfl⟩
          · intro β g
            rw [runBind hrun1, runBind (runPure _ lst1), rawNatLitC_eq, ← ho1abs]
            simp only [Option.map_some]
            rw [runBind hrun2, runBind (runPure _ lst2), rawNatLitC_eq, ← ho2abs]
            simp only [Option.map_some]

/-- `ConLeche/Cached/CoreC.lean:92-152` — **`reduce_nat_lits_i` refines the
cited two-literal read** (`core_c.rs:312`), `natLitsI` above. -/
theorem reduce_nat_lits_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim (Option.map (fun p : ron.nat.Nat × ron.nat.Nat => (Nat.toNat p.1, Nat.toNat p.2)))
      (fun o => ∀ p, o = some p → Nat.NatWF p.1 ∧ Nat.NatWF p.2)
      (fun st fe => cached.core_c.reduce_nat_lits_i mode fuel st fe d a b)
      (fun lfe => natLitsI (knot mode lfe fuel.val) d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfwf hfrel st r st' hwf hok lst hrel
  obtain ⟨lst1, hrel1, hwf1, hnwf, hrun⟩ := lits_replay hw d ha hb hfwf hfrel hwf hok hrel
  exact ⟨lst1, hrun (fun x => pure x), hrel1, hwf1, hnwf⟩

/-- `ConLeche/Cached/CoreC.lean:92-152` — **`reduce_nat_bin_i` refines the
cited certified-operation arm** (`core_c.rs:291`), `natBinI` above. -/
theorem reduce_nat_bin_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {c : name.Name} {a b : expr.Expr}
    (hc : NameWF c) (ha : ExprWF a) (hb : ExprWF b) :
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.reduce_nat_bin_i mode fuel st fe d c a b)
      (fun lfe => natBinI (knot mode lfe fuel.val) d.val (absName c)
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfwf hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.reduce_nat_bin_i at hok
  simp only [natBinI]
  obtain ⟨rr, st1, hl, hok⟩ := bindP hok
  cases rr with
  | Err err => have := Result.ok_injective hok; simp at this
  | Ok o =>
    obtain ⟨lst1, hrel1, hwf1, hnwf, hrun⟩ := lits_replay hw d ha hb hfwf hfrel hwf hl hrel
    cases o with
    | none =>
      have h2 := Result.ok_injective hok
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨lst1, ?_, hrel1, hwf1, by simp⟩
      exact hrun (fun o => match o with
        | some p => match ConLeche.natOpResult (absName c) p.1 p.2 with
          | some x => do
            let r ← pure x
            pure (some r)
          | none => pure none
        | none => pure none)
    | some p =>
      obtain ⟨n1, n2⟩ := p
      obtain ⟨hn1wf, hn2wf⟩ := hnwf (n1, n2) rfl
      -- The fold's own `core::result::Result` layer (task #61): the bind's
      -- value is `nat_op_result`'s verdict, and `hok` pins it to `.Ok r`, so
      -- the `.Err` rung -- a shift amount beyond `u64` -- never reaches the
      -- conclusion (DESIGN.md §3.5 claims nothing on failure).
      obtain ⟨r1, ho1, hok⟩ := bind_eq_ok_iff.mp hok
      have h2 := Result.ok_injective hok
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have hspec := CoreK.nat_op_result_refines hc hn1wf hn2wf CoreK.natOpPinned ho1
      have hg := hrun (β := Option ConLeche.Expr) (fun o => match o with
        | some q => match ConLeche.natOpResult (absName c) q.1 q.2 with
          | some x => do
            let r ← pure x
            pure (some r)
          | none => pure none
        | none => pure none)
      simp only [Option.map_some] at hg
      cases r with
      | some x =>
        obtain ⟨hx, hxwf⟩ := hspec.1 x rfl
        refine ⟨lst1, ?_, hrel1, hwf1, ?_⟩
        · rw [hg]
          simp only [hx]
          rfl
        · intro e' he'
          simp only [Option.some.injEq] at he'
          exact he' ▸ hxwf
      | none =>
        refine ⟨lst1, ?_, hrel1, hwf1, by simp⟩
        rw [hg]
        simp only [hspec.2 rfl]
        rfl

/-! ## `reduce_nat_i` — literal acceleration -/

/-- **The `natOpWfNames` arm** (`CoreC.lean:139-148`): a `Nat` operation whose
equations are *not* stored is still read for two literals, and two literals
make the reduction one the port does not implement — an error, so nothing is
claimed of it (DESIGN.md §3.5).  `core_c.rs` spells this arm twice (once under
a head that is none of the fourteen, once under one whose equations are
missing) where `reduceNatI` writes it once, so it is proved here once and used
twice.  The message is a parameter: only the error *constructor* matters, and
the two sides spell the text differently. -/
private theorem wf_arm {mode : env.CheckMode} {fuel : Std.U64} {msg : String}
    (hw : Wrappers mode fuel) (d : Std.U64) {c : name.Name} {a b : expr.Expr}
    (hc : NameWF c) (ha : ExprWF a) (hb : ExprWF b)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hfwf : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    {st st' : cached.state_c.CState} {r : Option expr.Expr} (hwf : StateWF st)
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst)
    (hok : (do
        let v1 ← core_k.nat_op_wf_names
        let b3 ← name.contains v1 c
        if b3 = true then do
            let b4 ← core_k.nat_lit_supported fe
            if b4 = true then do
                let (r1, st1) ← cached.core_c.reduce_nat_lits_i mode fuel st fe d a b
                match r1 with
                | core.result.Result.Ok o =>
                  match o with
                  | none => ok (core.result.Result.Ok none, st1)
                  | some _ => do
                    let s ← lift cached.core_c.reduce_nat_i.M.to_slice
                    let v2 ← core_types.code_points s
                    let ce ← core_types.not_implemented v2
                    ok (core.result.Result.Err ce, st1)
                | core.result.Result.Err err => ok (core.result.Result.Err err, st1)
              else ok (core.result.Result.Ok none, st)
          else ok (core.result.Result.Ok none, st))
        = ok (core.result.Result.Ok r, st')) :
    ∃ lst', StateT.run
        (show ConLeche.Cached.CheckCM (Option ConLeche.Expr) from
          if ConLeche.natOpWfNames.contains (absName c) = true ∧
            ConLeche.natLitSupportedF lfe = true then do
          let w₁ ← (knot mode lfe fuel.val).whnf d.val (absExpr a)
          match ← pure (ConLeche.Cached.rawNatLitC? w₁) with
          | some _ => do
            let w₂ ← (knot mode lfe fuel.val).whnf d.val (absExpr b)
            match ← pure (ConLeche.Cached.rawNatLitC? w₂) with
            | some _ => throw (ConLeche.CheckError.notImplemented msg)
            | none => pure none
          | none => pure none
          else pure none) lst
        = Except.ok (Option.map absExpr r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' ∧ ∀ e', r = some e' → ExprWF e' := by
  obtain ⟨v1, hv1, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hv1abs, hv1wf⟩ := CoreK.nat_op_wf_names_refines hv1
  obtain ⟨b3, hb3, hok⟩ := bind_eq_ok_iff.mp hok
  have hb3eq : b3 = ConLeche.natOpWfNames.contains (absName c) := by
    rw [Name.contains_refines hv1wf hc hb3, hv1abs]
  cases b3 with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hok
    rw [if_neg (fun hcon => by rw [hcon.1] at hb3eq; exact Bool.noConfusion hb3eq)]
    have h2 := Result.ok_injective hok
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨lst, by simp, hrel, hwf, by simp⟩
  | true =>
    simp only [if_true] at hok
    obtain ⟨b4, hb4, hok⟩ := bind_eq_ok_iff.mp hok
    have hb4eq := CoreK.nat_lit_supported_refines CoreK.pinnedBasisNames
      (FindAgree.of_rel hfrel hfwf) (FindWF.of_wf hfwf) hb4
    cases b4 with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_neg (fun hcon => by rw [hcon.2] at hb4eq; exact Bool.noConfusion hb4eq)]
      have h2 := Result.ok_injective hok
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨lst, by simp, hrel, hwf, by simp⟩
    | true =>
      simp only [if_true] at hok
      rw [if_pos ⟨hb3eq.symm, hb4eq.symm⟩]
      obtain ⟨rr, st1, hl, hok⟩ := bindP hok
      cases rr with
      | Err err => have := Result.ok_injective hok; simp at this
      | Ok o =>
        obtain ⟨lst1, hrel1, hwf1, hnwf, hrun⟩ := lits_replay hw d ha hb hfwf hfrel hwf hl hrel
        cases o with
        | some p =>
          exfalso
          obtain ⟨s, hs, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨v2, hv2, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
          have := Result.ok_injective hok
          simp at this
        | none =>
          have h2 := Result.ok_injective hok
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨lst1, ?_, hrel1, hwf1, by simp⟩
          exact hrun (fun o => match o with
            | some _ => throw (ConLeche.CheckError.notImplemented msg)
            | none => pure none)

/-- `expr::literal_nat` builds the `NatVal` literal. -/
private theorem literal_nat_eq {n : ron.nat.Nat} {l : expr.Literal}
    (h : expr.literal_nat n = ok l) : l = .NatVal n := by
  rw [expr.literal_nat] at h
  simp only [bind_eq_ok_iff, ptr_new_eq, Result.ok.injEq, exists_eq_left'] at h
  exact h.symm

/-- `ConLeche/Cached/CoreC.lean:93` — **`reduce_nat_i` refines `reduceNatI`**
(`core_c.rs:226`): `Nat.succ` of a literal packed back into a literal, and the
fourteen binary operations folded on literal arguments. -/
theorem reduce_nat_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.reduce_nat_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.reduceNatI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := by
  intro fe lfe hfwf hfrel st r st' hwf hok lst hrel
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfrel hfwf
  have hfw : FindWF fe := FindWF.of_wf hfwf
  unfold cached.core_c.reduce_nat_i at hok
  simp only [arc_deref_eq, bind_tc_ok] at hok
  simp only [ConLeche.Cached.reduceNatI, CoreK.absExpr_kind e]
  cases hke : e._0.kind
  all_goals rw [hke] at hok
  case App f b =>
    obtain ⟨hfw', hbw⟩ := CoreK.ExprWF.app_children he hke
    simp only [absExprKind, CoreK.absExpr_kind f] at hok ⊢
    cases hkf : f._0.kind
    all_goals rw [hkf] at hok
    case Const c us =>
      obtain ⟨hcw, husw⟩ := CoreK.ExprWF.const_children hfw' hkf
      simp only [absExprKind] at hok ⊢
      by_cases hlen : alloc.vec.Vec.len us = 0#usize
      · rw [if_pos hlen] at hok
        rw [show absLevels us = [] from by
          simp only [absLevels]
          rw [List.eq_nil_of_length_eq_zero (show us.val.length = 0 by scalar_tac)]
          rfl]
        dsimp only
        rw [runBind (runPure (absName c) lst)]
        obtain ⟨nm, hnm, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨hnmabs, hnmwf⟩ := CoreK.pinned_nat_succ_name nm hnm
        obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
        have hb1eq : b1 = decide (absName c = ConLeche.natSuccName) := by
          rw [Name.beq_refines hcw hnmwf hb1, hnmabs]
        by_cases hsucc : absName c = ConLeche.natSuccName
        · rw [show b1 = true from by rw [hb1eq, hsucc]; simp] at hok
          simp only [if_true] at hok
          obtain ⟨b2, hb2, hok⟩ := bind_eq_ok_iff.mp hok
          have hb2eq := CoreK.nat_lit_supported_refines CoreK.pinnedBasisNames hfa hfw hb2
          cases b2 with
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok
            rw [if_neg (by simp [← hb2eq])]
            have h2 := Result.ok_injective hok
            simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
            obtain ⟨rfl, rfl⟩ := h2
            exact ⟨lst, by simp, hrel, hwf, by simp⟩
          | true =>
            simp only [if_true] at hok
            rw [if_pos ⟨hsucc, hb2eq.symm⟩]
            obtain ⟨rr, st1, hw1, hok⟩ := bindP hok
            cases rr with
            | Err err => have := Result.ok_injective hok; simp at this
            | Ok wa =>
              obtain ⟨lst1, hrun1, hrel1, hwf1, hwawf⟩ :=
                (hw.whnfSim d hbw).apply hwf hfwf hw1 hrel hfrel
              rw [runBind hrun1, runBind (runPure _ lst1), rawNatLitC_eq]
              obtain ⟨o, ho, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨hoabs, howf⟩ :=
                CoreK.raw_nat_lit_refines hwawf CoreK.pinned_nat_zero_name ho
              rw [← hoabs]
              cases o with
              | none =>
                have h2 := Result.ok_injective hok
                simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
                obtain ⟨rfl, rfl⟩ := h2
                exact ⟨lst1, by simp, hrel1, hwf1, by simp⟩
              | some n1 =>
                simp only [bind_eq_ok_iff] at hok
                obtain ⟨n2, hn2, n3, hn3, l, hl, e1, hlit, hok⟩ := hok
                have h2 := Result.ok_injective hok
                simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
                obtain ⟨rfl, rfl⟩ := h2
                have hn3v : Nat.toNat n3 = Nat.toNat n1 + 1 := by
                  rw [(Nat.add_refines hn3).1, (Nat.one_refines hn2).1]
                have habs : absExpr e1 = ConLeche.Expr.lit (.natVal (Nat.toNat n1 + 1)) := by
                  rw [Expr.lit_refines hlit, literal_nat_eq hl]
                  simp only [absLiteral]
                  rw [hn3v]
                refine ⟨lst1, ?_, hrel1, hwf1, ?_⟩
                · simp only [Option.map_some, runBind (runPure _ lst1), runPure, habs]
                · intro e' he'
                  simp only [Option.some.injEq] at he'
                  exact he' ▸ Expr.lit_wf (by rw [literal_nat_eq hl]; exact (Nat.add_refines hn3).2)
                    hlit
        · rw [show b1 = false from by rw [hb1eq]; simp [hsucc]] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_neg (by simp [hsucc])]
          have h2 := Result.ok_injective hok
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨lst, by simp, hrel, hwf, by simp⟩
      · rw [if_neg hlen] at hok
        obtain ⟨x, xs, hus⟩ : ∃ x xs, (us : alloc.vec.Vec level.Level).val = x :: xs := by
          cases hus : (us : alloc.vec.Vec level.Level).val with
          | nil => exact absurd (HashMap.vec_len_eq_zero_iff.mpr hus) hlen
          | cons x xs => exact ⟨x, xs, rfl⟩
        rw [show absLevels us = absLevel x :: xs.map absLevel from by
          simp only [absLevels, hus, List.map_cons]]
        have h2 := Result.ok_injective hok
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨lst, by simp, hrel, hwf, by simp⟩
    case App g a =>
      obtain ⟨hgw, haw⟩ := CoreK.ExprWF.app_children hfw' hkf
      simp only [absExprKind, CoreK.absExpr_kind g] at hok ⊢
      cases hkg : g._0.kind
      all_goals rw [hkg] at hok
      case Const c us =>
        obtain ⟨hcw, huswg⟩ := CoreK.ExprWF.const_children hgw hkg
        simp only [absExprKind] at hok ⊢
        by_cases hlen : alloc.vec.Vec.len us = 0#usize
        · rw [if_neg (show ¬((alloc.vec.Vec.len us != 0#usize) = true) by simp [hlen])] at hok
          rw [show absLevels us = [] from by
            simp only [absLevels]
            rw [List.eq_nil_of_length_eq_zero
              (show (us : alloc.vec.Vec level.Level).val.length = 0 by
                rw [HashMap.vec_len_eq_zero_iff.mp hlen]; rfl)]
            rfl]
          dsimp only
          rw [runBind (runPure (absName c) lst)]
          obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
          have hb1eq := CoreK.is_nat_bin_op_refines hcw hb1
          cases b1 with
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok
            have hnD := of_decide_eq_false hb1eq.symm
            rw [if_neg (fun hcon => hnD hcon.1)]
            exact wf_arm hw d hcw haw hbw hfwf hfrel hwf hrel hok
          | true =>
            simp only [if_true] at hok
            obtain ⟨b2, hb2, hok⟩ := bind_eq_ok_iff.mp hok
            have hb2eq := CoreK.nat_op_stored_refines hfa hcw hb2
            have hD : absName c = ConLeche.natAddName ∨ absName c = ConLeche.natSubName ∨
                absName c = ConLeche.natMulName ∨ absName c = ConLeche.natPowName ∨
                absName c = ConLeche.natBeqName ∨ absName c = ConLeche.natBleName ∨
                absName c = ConLeche.natDivName ∨ absName c = ConLeche.natModName ∨
                absName c = ConLeche.natGcdName ∨ absName c = ConLeche.natLandName ∨
                absName c = ConLeche.natLorName ∨ absName c = ConLeche.natXorName ∨
                absName c = ConLeche.natShiftLeftName ∨
                absName c = ConLeche.natShiftRightName := of_decide_eq_true hb1eq.symm
            cases b2 with
            | true =>
              simp only [if_true] at hok
              rw [if_pos ⟨hD, hb2eq.symm⟩]
              obtain ⟨lst', hrun, hrel', hwf', hrwf⟩ :=
                (reduce_nat_bin_i_refines hw d hcw haw hbw).apply hwf hfwf hok hrel hfrel
              exact ⟨lst', hrun, hrel', hwf', hrwf⟩
            | false =>
              simp only [Bool.false_eq_true, if_false] at hok
              rw [if_neg (fun hcon => by rw [hcon.2] at hb2eq; exact Bool.noConfusion hb2eq)]
              exact wf_arm hw d hcw haw hbw hfwf hfrel hwf hrel hok
        · rw [if_pos (show (alloc.vec.Vec.len us != 0#usize) = true by simp [hlen])] at hok
          obtain ⟨x, xs, hus⟩ : ∃ x xs, (us : alloc.vec.Vec level.Level).val = x :: xs := by
            cases hus : (us : alloc.vec.Vec level.Level).val with
            | nil => exact absurd (HashMap.vec_len_eq_zero_iff.mpr hus) hlen
            | cons x xs => exact ⟨x, xs, rfl⟩
          rw [show absLevels us = absLevel x :: xs.map absLevel from by
            simp only [absLevels, hus, List.map_cons]]
          have h2 := Result.ok_injective hok
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨lst, by simp, hrel, hwf, by simp⟩
      all_goals
        simp only [absExprKind]
        have h2 := Result.ok_injective hok
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨lst, by simp, hrel, hwf, by simp⟩
    all_goals
      simp only [absExprKind]
      have h2 := Result.ok_injective hok
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨lst, by simp, hrel, hwf, by simp⟩
  all_goals
    simp only [absExprKind]
    have h2 := Result.ok_injective hok
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨lst, by simp, hrel, hwf, by simp⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The two entry points of the group, on Lean's own three axioms and nothing else:
no `sorryAx` (task #61), no Aeneas library axiom, nothing from con-leche. -/

/--
info: 'ConRon.Refine.Core.unfold_definition_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unfold_definition_i_refines

/--
info: 'ConRon.Refine.Core.reduce_nat_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reduce_nat_i_refines

end ConRon.Refine.Core



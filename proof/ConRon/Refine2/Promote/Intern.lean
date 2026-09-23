/-
# `ConRon.Refine2.Promote.Intern` — Theorem 2 for `arena::intern`

**Task #97-P5-Checker**, deliverable 1's first half (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/intern.rs`: con-leche's pinned VALUES into the
store — the basis blocks, the standard- and compiler-trust axiom pins and the
`Nat`-operation pin variants, which DESIGN §8.7 rules (B) IMPORTS rather than
copies, so that the twins above this module (`Arena/Basis.lean`,
`Arena/StdAxioms.lean`, `Arena/TrustAxioms.lean`, `Arena/NatOpPinSet.lean`)
are one line each: *the con-leche constant, interned*.

## The twin is two modules, not one

`Arena/Intern.lean` is five wrappers; the WALK is
`Arena/Frontend/Readback.lean`'s intern direction (`internExprGo`,
`internCV`, `internCI`, `internCIList`, `internDecl`), because the modeller
seam needs exactly the same direction and wrote it memoised.  So the
`_go`-shaped Rust functions are stated against `Frontend.*` and the five
fresh-memo entries against `Arena/Intern.lean`'s own wrappers.

## The one thing this tier's statements need that no earlier tier did

**Every argument is a con-leche VALUE**, and `Refine/Abs.lean`'s abstractions
of those are exact on WELL-FORMED values only — `absName` on a `Name` whose
strings are valid code points, `absExpr` on an `Expr` whose literals and
binder metadata are, and so on up to `ConstantInfoWF` and `DeclarationWF`.
That is the same restriction `TblRel`'s `RelOn P` carries (task #97-P5-0's
rule 4) and it is why `EMemoRel`'s `P` is `ExprWF`.  Each statement therefore
carries the WF of its own subject; the callers are the pin modules, and
`Refine/Pins*.lean` is where a pin's well-formedness is proved — so the
obligation lands where it is already discharged.

## Lockstep (task #97-T2-LOCKSTEP lane Promote)

All closed, over `AStateRel₀`/`AStateInv` and the Rust-side key predicates
(`EMemoRel` now carries `KeysOk ExprWF`, which the memo probe needs).  The
walks return their memo OUTSIDE the `Result`, so they are stated in `LSM`,
`Lockstep.LS` with that memo (below); a fresh-memo entry is `LSM.fresh`.  One
divergence found and fixed in the twin (P1: the projection arm's order,
`internExprGo`).
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Arena.Intern
import ConRon.Refine2.Promote.Prims
import ConRon.Refine.Env

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (ExprWF ExprsWF NameWF NamesWF LevelWF LevelsWF
  ConstantValWF ConstantInfoWF ConstantInfosWF DeclarationWF RecRuleWF
  RecRulesWF IndCapsWF ProjTableWF RecRuleFireWF)
open ConRon.Refine.HashMap2 (Inv RelOn)

/-! ## The memo itself -/

/-- `arena::intern::memo_empty` is the twin's `(∅ : EMemo)`. -/
theorem memo_empty_refines {o}
    (hrun : arena.intern.memo_empty = ok o) :
    EMemoRel o (∅ : Frontend.EMemo) := by
  obtain ⟨hinv, hnil, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable) hrun
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv,
    ConRon.Refine.HashMap2.KeysOk_of_nil hnil⟩

/-- `expr::beq` never lies about well-formed terms: the memo's key dictionary
decides raw equality on `ExprWF` keys (`absExpr` is injective there). -/
theorem expr_eq2Fwd :
    ConRon.Refine.HashMap.Eq2Fwd kernel.expr.Expr.Insts.Con_ron_coreRonHashmapEq2 ExprWF := by
  intro a b c ha hb h
  rw [ConRon.Refine.Expr.eq2_refines ha hb h]
  exact decide_eq_decide.mpr
    ⟨fun hc => ConRon.Refine.Expr.absExpr_injective ha hb hc, fun hc => by rw [hc]⟩

/-- `arena::intern::memo_get` is the twin's `m[e]?` — the probe extraction
rule 5 gave its own function. -/
theorem memo_get_refines {rm lm} {e : kernel.expr.Expr} {o}
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : arena.intern.memo_get rm e = ok o) :
    o.map absEIdx = lm[ConRon.Refine.absExpr e]? := by
  rw [arena.intern.memo_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf expr_eq2Fwd hm.2.1 hm.2.2 hwf hr
  rw [← hm.1 e hwf, ← hto]
  cases r with
  | none => cases Result.ok_injective hrun; rfl
  | some h =>
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    rw [dupId_eidx _ _ hx]

/-- The memo's write: `HashMap2::insert` at a well-formed key is the twin's
`insert` at its abstraction. -/
theorem memo_insert_refines {rm lm} {e : kernel.expr.Expr} {h : arena.handle.EIdx} {old rm'}
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : ron.hashmap2.HashMap2.insert kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      kernel.expr.Expr.Insts.Con_ron_coreRonHashmapEq2 rm e h = ok (old, rm')) :
    EMemoRel rm' (lm.insert (ConRon.Refine.absExpr e) (absEIdx h)) := by
  obtain ⟨hinv', -, -, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_wf expr_eq2Fwd hm.2.1 hm.2.2 hwf hrun
  obtain ⟨hrel', hkeys'⟩ := ConRon.Refine.HashMap2.Rel_insert_wf expr_eq2Fwd
    (fun a b ha hb hab => ConRon.Refine.Expr.absExpr_injective ha hb hab)
    hm.2.1 hm.2.2 hm.1 hwf hrun
  exact ⟨hrel', hinv', hkeys'⟩

/-! ## The walk's judgement

`arena::intern`'s walks return their memo OUTSIDE the `Result` (a `&mut`
borrow comes back whatever happened), so they are not `Lockstep.LS`'s shape.
`LSM` is `LS` with that memo: an `Ok a` in memo `mm` is matched by a twin
answer `(s, b)` with `EMemoRel mm s` and `R a b`, an `Err` by the twin's throw
at the same kind; its bind rules are `LS`'s, one per callee shape (a walk, a
state-threading callee, a Rust-only step).  `EOut`/`SimEM` is `LSM` at a
Rust equation (`LSM.toSimEM`). -/

namespace Lockstep

/-- What an intern walk's outcome claims about a twin run. -/
def MOut {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (o : core.result.Result α kernel.core_types.CheckError) (st' : arena.monad.AState)
    (mm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)
    (y : Except Arena.CheckError ((Frontend.EMemo × β) × AState)) : Prop :=
  match o with
  | .Ok a => ∃ s b lst', y = .ok ((s, b), lst') ∧ EMemoRel mm s ∧ R a b ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | .Err e => AErrSim e y

/-- **The judgement of an `arena::intern` walk.** -/
def LSM {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx))
    (lst : AState) (x : AM (Frontend.EMemo × β)) : Prop :=
  ∀ o st' mm, m = ok (o, st', mm) → MOut pers R o st' mm (x.run lst)

theorem LSM.toSimEM {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM (Frontend.EMemo × β)} {o}
    (h : LSM pers (fun a b => b = A a) m lst x) (hm : m = ok o) : SimEM A pers lst o x := by
  obtain ⟨o, st', mm⟩ := o
  have := h o st' mm hm
  show EOut A pers lst o st' mm (x.run lst)
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨s, b, lst', hx, hm, rfl, h1, h2⟩ := this
    exact ⟨s, lst', hx, hm, h1, h2⟩

theorem LSM.bindM {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState ×
        ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM (Frontend.EMemo × β)} {g : Frontend.EMemo × β → AM (Frontend.EMemo × δ)}
    (hf : LSM pers R₁ f lst x)
    (he : ∀ e st1 m1 o st' mm, k (.Err e, st1, m1) = ok (o, st', mm) → o = .Err e)
    (hk : ∀ a b s st1 m1 lst1, EMemoRel m1 s → R₁ a b → AStateRel₀ pers st1 lst1 →
      AStateInv pers st1 → LSM pers R (k (.Ok a, st1, m1)) lst1 (g (s, b))) :
    LSM pers R (f >>= k) lst (x >>= g) := by
  intro o st' mm hm
  obtain ⟨⟨r, st1, m1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r st1 m1 hf1
  cases r with
  | Err e =>
    have := he e st1 m1 o st' mm hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨s, b, lst1, hx1, hms, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b s st1 m1 lst1 hms hR hrel hinv o st' mm hk1

theorem LSM.bindS {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState ×
        ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM β} {g : β → AM (Frontend.EMemo × δ)}
    (hf : LS pers R₁ f lst x)
    (he : ∀ e st1 o st' mm, k (.Err e, st1) = ok (o, st', mm) → o = .Err e)
    (hk : ∀ a b st1 lst1, R₁ a b → AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      LSM pers R (k (.Ok a, st1)) lst1 (g b)) :
    LSM pers R (f >>= k) lst (x >>= g) := by
  intro o st' mm hm
  obtain ⟨⟨r, st1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r st1 hf1
  cases r with
  | Err e =>
    have := he e st1 o st' mm hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b st1 lst1 hR hrel hinv o st' mm hk1

/-- A state-threading callee in tail position, the memo handed back beside it. -/
theorem LSM.tailS {α β : Type} {pers : arena.store.PersTier} {R₁ R : α → β → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState →
      Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
        ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {mm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx} {s : Frontend.EMemo}
    {lst : AState} {x : AM β}
    (hf : LS pers R₁ f lst x) (hk : ∀ r st, k (r, st) = ok (r, st, mm))
    (hms : EMemoRel mm s) (hR : ∀ a b, R₁ a b → R a b) :
    LSM pers R (f >>= k) lst (x >>= fun b => pure (s, b)) := by
  intro o st' mm' hm
  obtain ⟨⟨r, st1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  rw [hk] at hk1
  simp only [Result.ok.injEq, Prod.mk.injEq] at hk1
  obtain ⟨rfl, rfl, rfl⟩ := hk1
  have h1 := hf r st1 hf1
  cases r with
  | Err e => exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hRb, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact ⟨s, b, lst1, rfl, hms, hR _ _ hRb, hrel, hinv⟩

theorem LSM.bindP {α γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    {f : Result α}
    {k : α → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM (Frontend.EMemo × δ)}
    (hk : ∀ a, f = ok a → LSM pers R (k a) lst x) : LSM pers R (f >>= k) lst x := by
  intro o st' mm hm
  obtain ⟨a, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact hk a hf1 o st' mm hk1

theorem LSM.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {a : α} {b : β} {st : arena.monad.AState} {lst : AState}
    {mm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx} {s : Frontend.EMemo}
    (hms : EMemoRel mm s) (hR : R a b) (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSM pers R (ok (.Ok a, st, mm)) lst (Pure.pure (s, b)) := by
  intro o st' mm' hm
  cases Result.ok_injective hm
  exact ⟨s, b, lst, rfl, hms, hR, hrel, hinv⟩

theorem LSM.twin_eq {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x y : AM (Frontend.EMemo × β)} (h : LSM pers R m lst x) (hxy : x = y) :
    LSM pers R m lst y := hxy ▸ h

end Lockstep

namespace Lockstep

/-- A fresh-memo entry: `memo_empty`, the walk, the memo dropped. -/
theorem LSM.fresh {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {walk : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx →
      Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
        ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM (Frontend.EMemo × β)}
    (h : ∀ rm, EMemoRel rm (∅ : Frontend.EMemo) → LSM pers R (walk rm) lst x) :
    LS pers R (do
        let m ← arena.intern.memo_empty
        let (r, st1, _) ← walk m
        ok (r, st1)) lst (do Pure.pure (← x).2) := by
  intro o st' hm
  obtain ⟨m0, hm0, hrest⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨⟨r, st1, mm⟩, hw, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrest
  have hk' := Result.ok_injective hk
  simp only [Prod.mk.injEq] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  have h1 := h m0 (memo_empty_refines hm0) r st1 mm hw
  cases r with
  | Err e => exact errSim_bind h1
  | Ok a =>
    obtain ⟨s, b, lst', hx, -, hR, h2, h3⟩ := h1
    refine ⟨b, lst', ?_, hR, h2, h3⟩
    rw [run_bind_ok hx]
    rfl

end Lockstep

/-- The error arm of every bind below: the port returns the callee's `Err`
unchanged. -/
macro "lsm_err" : tactic => `(tactic| (
  intros
  rename_i h
  have h2 := Result.ok_injective h
  simp only [Prod.mk.injEq] at h2
  exact h2.1.symm))

/-! ## The expression walk

`Frontend.internExprGo`'s ten clauses: four leaves that do not touch the memo
(`bvar`, `sort`, `const`, `lit` — the store's own cons table already answers a
repeat in `O(1)`) and six compounds that probe it.  The port splits a
compound's arms past the probe off into `intern_expr_node` (extraction rule
5); its twin is `internExprNodeSpec`, the twin's own arms WITHOUT the probe and
the memo write (the old statement of `intern_expr_node_refines` put the write
in, and was false: the port's node returns the memo before its caller
records `e`).

**Divergence P1 (task #97-T2-LOCKSTEP lane Promote), fixed in the twin.**
`intern_expr_node`'s projection arm interns the NAME first and then the
subterm; `internExprGo`'s did the subterm first.  Both write the name store
(a subterm may hold constants), so the two orders hand out different name
handles.  `Arena/Frontend/Readback.lean` now follows the port; Theorem 1's
`internExprGo_sstep` took the reordering. -/

/-- The twin's compound arms past the probe (`intern_expr_node`'s twin); a
leaf is the walk itself, as the port's node falls back to `intern_expr_go`. -/
def internExprNodeSpec (m : Frontend.EMemo) : ConLeche.Expr → AM (Frontend.EMemo × EIdx)
  | .fvar i ty => do
    let (m, t) ← Frontend.internExprGo m ty
    let h ← internE (.fvar i t)
    pure (m, h)
  | .app f a => do
    let (m, hf) ← Frontend.internExprGo m f
    let (m, ha) ← Frontend.internExprGo m a
    let h ← internE (.app hf ha)
    pure (m, h)
  | .lam ty b bi => do
    let (m, ht) ← Frontend.internExprGo m ty
    let (m, hb) ← Frontend.internExprGo m b
    let h ← internE (.lam ht hb bi)
    pure (m, h)
  | .forallE ty b bi => do
    let (m, ht) ← Frontend.internExprGo m ty
    let (m, hb) ← Frontend.internExprGo m b
    let h ← internE (.forallE ht hb bi)
    pure (m, h)
  | .letE ty v b => do
    let (m, ht) ← Frontend.internExprGo m ty
    let (m, hv) ← Frontend.internExprGo m v
    let (m, hb) ← Frontend.internExprGo m b
    let h ← internE (.letE ht hv hb)
    pure (m, h)
  | .proj n i sub => do
    let hn ← internName n
    let (m, hs) ← Frontend.internExprGo m sub
    let h ← internE (.proj hn i hs)
    pure (m, h)
  | e => Frontend.internExprGo m e

/-- The twin's probe: a hit answers, a miss runs the arm and records it. -/
def internProbe (m : Frontend.EMemo) (e : ConLeche.Expr)
    (node : AM (Frontend.EMemo × EIdx)) : AM (Frontend.EMemo × EIdx) :=
  match m[e]? with
  | some h => pure (m, h)
  | none => do
    let (m', h) ← node
    pure (m'.insert e h, h)

/-- A compound clause of `internExprGo` is the probe over its node arm. -/
theorem internExprGo_compound (m : Frontend.EMemo) (e : ConLeche.Expr)
    (hc : match e with
      | .bvar _ | .sort _ | .const _ _ | .lit _ => False
      | _ => True) :
    Frontend.internExprGo m e = internProbe m e (internExprNodeSpec m e) := by
  cases e <;> simp only at hc <;>
    simp only [Frontend.internExprGo, internProbe, internExprNodeSpec] <;>
    (split <;> rename_i heq <;> simp [heq, bind_assoc])

private theorem intern_e_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.ENodeView)
    (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m →
      ConRon.Refine.PropWhenWF m.pw) :
    Lockstep.LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e pers st v) lst
      (Arena.internE (absENodeView v)) :=
  Lockstep.LS.ofSim₀ fun _ h => intern_e_run₀ hrel hinv v hlit hpw h

private theorem intern_name_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : kernel.name.Name) (hwf : NameWF n) :
    Lockstep.LS pers (fun a b => b = absNIdx a) (arena.monad.intern_name pers st n) lst
      (Arena.internName (ConRon.Refine.absName n)) :=
  Lockstep.LS.ofSim₀ fun _ h => intern_name_run₀ hrel hinv hwf h

private theorem intern_level_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (u : kernel.level.Level) (hwf : LevelWF u) :
    Lockstep.LS pers (fun a b => b = absLIdx a) (arena.monad.intern_level pers st u) lst
      (Arena.internLevel (ConRon.Refine.absLevel u)) :=
  Lockstep.LS.ofSim₀ fun _ h => intern_level_run₀ hrel hinv hwf h

private theorem intern_levels_ls' {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (us : alloc.vec.Vec kernel.level.Level) (hwf : LevelsWF us) :
    Lockstep.LS pers (fun a b => b = absLsIdx a) (arena.monad.intern_levels pers st us) lst
      (Arena.internLevels (ConRon.Refine.absLevels us)) :=
  Lockstep.LS.ofSim₀ fun _ h => intern_levels_run₀ hrel hinv hwf h

/-- The Rust side of a node: `kernel.expr.view` of a constructor is its
kind. -/
macro "rust_view" : tactic => `(tactic| (
  simp only [ConRon.Refine.expr_view_eq, ConRon.Refine.arc_deref_eq, Aeneas.Std.bind_tc_ok,
    kernel.expr.Expr._0._simpLemma_, kernel.expr.ExprNode.kind._simpLemma_,
    kernel.expr.ExprView.ofKind]))

/-- The twin side of a node: `absExpr` of a constructor. -/
macro "twin_abs" : tactic => `(tactic|
  simp only [ConRon.Refine.absExpr, ConRon.Refine.absExprNode, ConRon.Refine.absExprKind])

open Lockstep in
/-- A compound node's probe, given its arm: the port's `memo_get`, `node`,
`insert` against the twin's `internProbe`. -/
private theorem intern_probe_ls {pers st lst rm lm} {e : kernel.expr.Expr}
    {node : Result (core.result.Result arena.handle.EIdx kernel.core_types.CheckError ×
      arena.monad.AState × ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {tnode : AM (Frontend.EMemo × EIdx)}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : EMemoRel rm lm)
    (hwf : ExprWF e) (hnode : LSM pers (fun a b => b = absEIdx a) node lst tnode) :
    LSM pers (fun a b => b = absEIdx a)
      (do
        let o ← arena.intern.memo_get rm e
        match o with
        | none =>
          let (r, st1, m1) ← node
          match r with
          | core.result.Result.Ok h =>
            let e1 ← kernel.expr.dup e
            let e2 ← arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h
            let (_, m2) ←
              ron.hashmap2.HashMap2.insert
                kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable
                kernel.expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m1 e1 e2
            ok (r, st1, m2)
          | core.result.Result.Err _ => ok (r, st1, m1)
        | some h => ok (core.result.Result.Ok h, st, rm))
      lst (internProbe lm (ConRon.Refine.absExpr e) tnode) := by
  refine LSM.bindP fun o ho => ?_
  have hget := memo_get_refines hm hwf ho
  cases o with
  | none =>
    have hn : lm[ConRon.Refine.absExpr e]? = none := by simpa using hget.symm
    simp only [internProbe, hn]
    refine LSM.bindM hnode (by lsm_err) ?_
    intro h h' s st1 m1 lst1 hms hh hrel1 hinv1
    subst hh
    refine LSM.bindP fun e1 he1 => ?_
    rw [ConRon.Refine.Expr.dup_eq he1]
    refine LSM.bindP fun e2 he2 => ?_
    rw [dupId_eidx _ _ he2]
    refine LSM.bindP fun p hp => ?_
    obtain ⟨old, m2⟩ := p
    exact LSM.pure (memo_insert_refines hms hwf hp) rfl hrel1 hinv1
  | some h =>
    have hs : lm[ConRon.Refine.absExpr e]? = some (absEIdx h) := by simpa using hget.symm
    simp only [internProbe, hs]
    exact LSM.pure hm rfl hrel hinv

open Lockstep in
private theorem intern_expr_aux (e : kernel.expr.Expr) (he : ExprWF e) :
    (∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st → EMemoRel rm lm →
      LSM pers (fun a b => b = absEIdx a) (arena.intern.intern_expr_go pers st rm e) lst
        (Frontend.internExprGo lm (ConRon.Refine.absExpr e))) ∧
    (∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st → EMemoRel rm lm →
      LSM pers (fun a b => b = absEIdx a) (arena.intern.intern_expr_node pers st rm e) lst
        (internExprNodeSpec lm (ConRon.Refine.absExpr e))) := by
  induction e, he using ConRon.Refine.ExprWF.ind_node with
  | bvar d i h =>
    have hgo : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_go pers st rm (.mk (.mk d (.Bvar i)))) lst
          (Frontend.internExprGo lm (ConRon.Refine.absExpr (.mk (.mk d (.Bvar i))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_go]; rust_view; twin_abs
      refine LSM.tailS ?_ (fun _ _ => rfl) hm (fun _ _ h => h)
      exact intern_e_ls' hrel hinv _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨hgo, fun hrel hinv hm => ?_⟩
    rw [arena.intern.intern_expr_node]; rust_view
    exact hgo hrel hinv hm
  | sort d u h =>
    have hu := ConRon.Refine.ExprWF.sort_kids h
    have hgo : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_go pers st rm (.mk (.mk d (.«Sort» u)))) lst
          (Frontend.internExprGo lm (ConRon.Refine.absExpr (.mk (.mk d (.«Sort» u))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_go]; rust_view; twin_abs
      simp only [Frontend.internExprGo]
      refine LSM.bindS (intern_level_ls' hrel hinv u hu) (by lsm_err) ?_
      intro a b st1 lst1 hR hrel1 hinv1
      subst hR
      refine LSM.tailS ?_ (fun _ _ => rfl) hm (fun _ _ h => h)
      exact intern_e_ls' hrel1 hinv1 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨hgo, fun hrel hinv hm => ?_⟩
    rw [arena.intern.intern_expr_node]; rust_view
    exact hgo hrel hinv hm
  | mk_const d n us h =>
    obtain ⟨hn, hus⟩ := ConRon.Refine.ExprWF.const_kids h
    have hgo : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_go pers st rm (.mk (.mk d (.Const n us)))) lst
          (Frontend.internExprGo lm (ConRon.Refine.absExpr (.mk (.mk d (.Const n us))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_go]; rust_view; twin_abs
      simp only [Frontend.internExprGo]
      refine LSM.bindS (intern_name_ls' hrel hinv n hn) (by lsm_err) ?_
      intro a b st1 lst1 hR hrel1 hinv1
      subst hR
      try simp only [ConRon.Refine.arc_deref_eq, Aeneas.Std.bind_tc_ok]
      refine LSM.bindS (intern_levels_ls' hrel1 hinv1 us hus) (by lsm_err) ?_
      intro a' b' st2 lst2 hR' hrel2 hinv2
      subst hR'
      refine LSM.tailS ?_ (fun _ _ => rfl) hm (fun _ _ h => h)
      exact intern_e_ls' hrel2 hinv2 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨hgo, fun hrel hinv hm => ?_⟩
    rw [arena.intern.intern_expr_node]; rust_view
    exact hgo hrel hinv hm
  | lit d l h =>
    have hl := ConRon.Refine.ExprWF.lit_kids h
    have hgo : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_go pers st rm (.mk (.mk d (.Lit l)))) lst
          (Frontend.internExprGo lm (ConRon.Refine.absExpr (.mk (.mk d (.Lit l))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_go]; rust_view; twin_abs
      simp only [Frontend.internExprGo]
      refine LSM.bindP fun l1 hl1 => ?_
      rw [ConRon.Refine.Expr.literal_dup_eq hl1]
      refine LSM.tailS ?_ (fun _ _ => rfl) hm (fun _ _ h => h)
      exact intern_e_ls' hrel hinv (.Lit l) (fun _ h => by injection h with h; subst h; exact hl)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨hgo, fun hrel hinv hm => ?_⟩
    rw [arena.intern.intern_expr_node]; rust_view
    exact hgo hrel hinv hm
  | fvar d idx ty h ih =>
    have hty := ConRon.Refine.ExprWF.fvar_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.Fvar idx ty)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.Fvar idx ty))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindM ((ih hty).1 hrel hinv hm) (by lsm_err) ?_
      intro a b s st1 m1 lst1 hms hR hrel1 hinv1
      subst hR
      refine LSM.tailS ?_ (fun _ _ => rfl) hms (fun _ _ h => h)
      exact intern_e_ls' hrel1 hinv1 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)
  | app d f a h ihf iha =>
    obtain ⟨hf, ha⟩ := ConRon.Refine.ExprWF.app_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.App f a)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.App f a))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindM ((ihf hf).1 hrel hinv hm) (by lsm_err) ?_
      intro a1 b1 s1 st1 m1 lst1 hms1 hR1 hrel1 hinv1
      subst hR1
      refine LSM.bindM ((iha ha).1 hrel1 hinv1 hms1) (by lsm_err) ?_
      intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
      subst hR2
      refine LSM.tailS ?_ (fun _ _ => rfl) hms2 (fun _ _ h => h)
      exact intern_e_ls' hrel2 hinv2 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)
  | lam d ty b bi h ihty ihb =>
    obtain ⟨hty, hb, hbi⟩ := ConRon.Refine.ExprWF.lam_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.Lam ty b bi)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.Lam ty b bi))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindM ((ihty hty).1 hrel hinv hm) (by lsm_err) ?_
      intro a1 b1 s1 st1 m1 lst1 hms1 hR1 hrel1 hinv1
      subst hR1
      refine LSM.bindM ((ihb hb).1 hrel1 hinv1 hms1) (by lsm_err) ?_
      intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
      subst hR2
      refine LSM.bindP fun bm hbm => ?_
      rw [ConRon.Refine.Expr.binder_meta_dup_eq hbm]
      refine LSM.tailS ?_ (fun _ _ => rfl) hms2 (fun _ _ h => h)
      exact intern_e_ls' hrel2 hinv2 (.Lam _ _ bi) (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h; exact hbi)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)
  | forall_e d ty b bi h ihty ihb =>
    obtain ⟨hty, hb, hbi⟩ := ConRon.Refine.ExprWF.forall_e_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.ForallE ty b bi)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.ForallE ty b bi))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindM ((ihty hty).1 hrel hinv hm) (by lsm_err) ?_
      intro a1 b1 s1 st1 m1 lst1 hms1 hR1 hrel1 hinv1
      subst hR1
      refine LSM.bindM ((ihb hb).1 hrel1 hinv1 hms1) (by lsm_err) ?_
      intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
      subst hR2
      refine LSM.bindP fun bm hbm => ?_
      rw [ConRon.Refine.Expr.binder_meta_dup_eq hbm]
      refine LSM.tailS ?_ (fun _ _ => rfl) hms2 (fun _ _ h => h)
      exact intern_e_ls' hrel2 hinv2 (.ForallE _ _ bi) (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h; exact hbi)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)
  | let_e d ty v b h ihty ihv ihb =>
    obtain ⟨hty, hv, hb⟩ := ConRon.Refine.ExprWF.let_e_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.LetE ty v b)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.LetE ty v b))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindM ((ihty hty).1 hrel hinv hm) (by lsm_err) ?_
      intro a1 b1 s1 st1 m1 lst1 hms1 hR1 hrel1 hinv1
      subst hR1
      refine LSM.bindM ((ihv hv).1 hrel1 hinv1 hms1) (by lsm_err) ?_
      intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
      subst hR2
      refine LSM.bindM ((ihb hb).1 hrel2 hinv2 hms2) (by lsm_err) ?_
      intro a3 b3 s3 st3 m3 lst3 hms3 hR3 hrel3 hinv3
      subst hR3
      refine LSM.tailS ?_ (fun _ _ => rfl) hms3 (fun _ _ h => h)
      exact intern_e_ls' hrel3 hinv3 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)
  | proj d sn i x h ihx =>
    obtain ⟨hsn, hx⟩ := ConRon.Refine.ExprWF.proj_kids h
    have hnode : ∀ {pers st lst rm lm}, AStateRel₀ pers st lst → AStateInv pers st →
        EMemoRel rm lm →
        LSM pers (fun a b => b = absEIdx a)
          (arena.intern.intern_expr_node pers st rm (.mk (.mk d (.Proj sn i x)))) lst
          (internExprNodeSpec lm (ConRon.Refine.absExpr (.mk (.mk d (.Proj sn i x))))) := by
      intro pers st lst rm lm hrel hinv hm
      rw [arena.intern.intern_expr_node]; rust_view; twin_abs
      simp only [internExprNodeSpec]
      refine LSM.bindS (intern_name_ls' hrel hinv sn hsn) (by lsm_err) ?_
      intro a1 b1 st1 lst1 hR1 hrel1 hinv1
      subst hR1
      refine LSM.bindM ((ihx hx).1 hrel1 hinv1 hm) (by lsm_err) ?_
      intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
      subst hR2
      refine LSM.tailS ?_ (fun _ _ => rfl) hms2 (fun _ _ h => h)
      exact intern_e_ls' hrel2 hinv2 _ (by intro _ h; cases h)
        (by intro _ _ _ h; rcases h with h | h <;> cases h)
    refine ⟨fun hrel hinv hm => ?_, hnode⟩
    rw [arena.intern.intern_expr_go]; rust_view
    rw [internExprGo_compound _ _ (by twin_abs <;> trivial)]
    exact intern_probe_ls hrel hinv hm h (hnode hrel hinv hm)

open Lockstep in
/-- **`intern_expr_go` ⊑ `Frontend.internExprGo`**, in the judgement shape. -/
theorem intern_expr_go_ls {pers st lst rm lm} {e : kernel.expr.Expr}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprWF e) :
    LSM pers (fun a b => b = absEIdx a) (arena.intern.intern_expr_go pers st rm e) lst
      (Frontend.internExprGo lm (ConRon.Refine.absExpr e)) :=
  (intern_expr_aux e hwf).1 hrel hinv hm

/-- `intern_expr_go` ⊑ `Frontend.internExprGo`. -/
theorem intern_expr_go_refines {pers st lst rm lm} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : arena.intern.intern_expr_go pers st rm e = ok o) :
    SimEM absEIdx pers lst o (Frontend.internExprGo lm (ConRon.Refine.absExpr e)) :=
  Lockstep.LSM.toSimEM (intern_expr_go_ls hrel hinv hm hwf) hrun

/-- `intern_expr_node` is task #97-P6-2's Rust-only split of `intern_expr_go`'s
six compound arms past the probe (extraction rule 5: the `view`'s loans are
dead at the memo's join), so it is stated against the twin's own arm before
the memo write (`internExprNodeSpec`). -/
theorem intern_expr_node_refines {pers st lst rm lm} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : arena.intern.intern_expr_node pers st rm e = ok o) :
    SimEM absEIdx pers lst o (internExprNodeSpec lm (ConRon.Refine.absExpr e)) :=
  Lockstep.LSM.toSimEM ((intern_expr_aux e hwf).2 hrel hinv hm) hrun

/-- `intern_expr` ⊑ `Arena.internExpr` — the fresh-memo entry. -/
theorem intern_expr_refines {pers st lst} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hwf : ExprWF e)
    (hrun : arena.intern.intern_expr pers st e = ok o) :
    Sim₀ absEIdx pers lst o (internExpr (ConRon.Refine.absExpr e)) := by
  rw [arena.intern.intern_expr] at hrun
  exact Lockstep.LS.toSim₀
    (Lockstep.LSM.fresh fun rm hm => intern_expr_go_ls hrel hinv hm hwf) hrun

theorem internExprList_pmapFrom (m : Frontend.EMemo) (l : List ConLeche.Expr)
    (acc : List EIdx) :
    pmapFrom Frontend.internExprGo m acc l =
      (do let (m, ys) ← Frontend.internExprList m l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ Frontend.internExprList (fun _ => rfl) (fun _ _ _ => rfl) l m acc

open Lockstep in
private theorem intern_expr_list_go_aux (n : Nat) :
    ∀ {pers st lst rm lm} (es : alloc.vec.Vec kernel.expr.Expr) (i : Std.Usize)
      (out : alloc.vec.Vec arena.handle.EIdx),
      es.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      EMemoRel rm lm → ExprsWF es →
      LSM pers (fun a b => b = a.val.map absEIdx)
        (arena.intern.intern_expr_list_go pers st rm es i out) lst
        (pmapFrom Frontend.internExprGo lm (out.val.map absEIdx)
          ((es.val.drop i.val).map ConRon.Refine.absExpr)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    rw [arena.intern.intern_expr_list_go, vecFrom_nil v _ i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_pos (by scalar_tac)]
    exact LSM.pure hm rfl hrel hinv
  | succ k ih =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    have hlt : i.val < v.val.length := by omega
    rw [arena.intern.intern_expr_list_go, vecFrom_cons v _ i hlt, pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_neg (by scalar_tac)]
    refine LSM.bindP fun x hx => ?_
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    subst hxv
    refine LSM.bindM (intern_expr_go_ls hrel hinv hm (hP _ (List.getElem_mem hlt)))
      (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindP fun out1 hout1 => ?_
    refine LSM.bindP fun i2 hi2 => ?_
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have h := ih v i2 out1 (by omega) hrel1 hinv1 hms hP
    rw [ConRon.Refine.vec_push_val hout1, hi2v] at h
    simpa [List.map_append] using h

open Lockstep in
/-- `intern_expr_list_go` ⊑ `pmapFrom internExprGo` — the cursor. -/
theorem intern_expr_list_go_ls {pers st lst rm lm}
    {es : alloc.vec.Vec kernel.expr.Expr} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprsWF es) :
    LSM pers (fun a b => b = a.val.map absEIdx)
      (arena.intern.intern_expr_list_go pers st rm es i out) lst
      (pmapFrom Frontend.internExprGo lm (out.val.map absEIdx)
        ((es.val.drop i.val).map ConRon.Refine.absExpr)) :=
  intern_expr_list_go_aux _ es i out rfl hrel hinv hm hwf

/-- `intern_expr_list_go` ⊑ `Frontend.internExprList` at the cursor.
**Restated by task #97-P5-Top** (the result abstracts by `absEIdxL` alone:
the walk accumulates into `out`; see `intern_name_list_go_refines`). -/
theorem intern_expr_list_go_refines {pers st lst rm lm}
    {es : alloc.vec.Vec kernel.expr.Expr} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprsWF es)
    (hrun : arena.intern.intern_expr_list_go pers st rm es i out = ok o) :
    SimEM absEIdxL pers lst o
      (do let (m, hs) ← Frontend.internExprList lm (absExprLFrom es i)
          pure (m, absEIdxL out ++ hs)) := by
  have h := intern_expr_list_go_ls (i := i) (out := out) hrel hinv hm hwf
  rw [internExprList_pmapFrom] at h
  exact Lockstep.LSM.toSimEM h hrun

/-- `intern_expr_list` ⊑ `Arena.internExprList`. -/
theorem intern_expr_list_refines {pers st lst}
    {es : alloc.vec.Vec kernel.expr.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hwf : ExprsWF es)
    (hrun : arena.intern.intern_expr_list pers st es = ok o) :
    Sim₀ absEIdxL pers lst o
      (internExprList (ConRon.Refine.absExprs es)) := by
  rw [arena.intern.intern_expr_list] at hrun
  have h := Lockstep.LSM.fresh (x := do
      let (m, ys) ← Frontend.internExprList (∅ : Frontend.EMemo) (ConRon.Refine.absExprs es)
      pure (m, ([] : List EIdx) ++ ys))
    (fun rm hm => by
      have h := intern_expr_list_go_ls (i := 0#usize) (out := alloc.vec.Vec.new _)
        hrel hinv hm hwf
      rw [internExprList_pmapFrom] at h
      simpa [ConRon.Refine.absExprs, alloc.vec.Vec.new] using h)
  refine Lockstep.LS.toSim₀ (Lockstep.LS.tail h ?_ (fun _ _ h => h)) hrun
  simp [internExprList, bind_assoc]

/-! ## The two handle-list walks that carry no memo

A name and a level are interned through `arena::monad`'s own cons tables, so
these two are plain `Sim`s at the cursor. -/

/-- `Refine/ExprOps.lean`'s `vec_index_getElem?`, which this file does not
import. -/
private theorem vec_index_getElem?' {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The name-list walk at the cursor, with its flag frame — the induction
`intern_name_list_go_refines` and `intern_name_list_flags` read their halves
off (task #97-P5-Top). -/
private theorem intern_name_list_go_aux (n : Nat) :
    ∀ {pers st lst} {ns : alloc.vec.Vec kernel.name.Name} {i : Std.Usize}
      {out : alloc.vec.Vec arena.handle.NIdx} {o},
      ns.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      NamesWF ns →
      arena.intern.intern_name_list_go pers st ns i out = ok o →
      Sim₀ absNIdxL pers lst o
        (do pure (absNIdxL out ++ (← Frontend.internNameList (absNameLFrom ns i)))) ∧
      FlagsEq st.store o.2.store := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst ns i out o hn hrel hinv hwf hrun
    rw [arena.intern.intern_name_list_go.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i hge
      have hlen : ns.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val ns; scalar_tac
      have ho := Result.ok_injective hrun
      subst ho
      refine ⟨?_, FlagsEq.refl _⟩
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      simp [absNameLFrom, List.drop_eq_nil_of_le hlen, Frontend.internNameList]
      rfl
    · rename_i hge
      have hlt : i.val < ns.val.length := by
        have := alloc.vec.Vec.len_val ns; scalar_tac
      obtain ⟨nm, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hnm : ns.val[i.val] = nm := by
        have hg := vec_index_getElem?' hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hnwf : ConRon.Refine.NameWF nm := hwf nm (hnm ▸ List.getElem_mem hlt)
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := q
      obtain ⟨hS, hF⟩ := intern_name_run'₀ nm hnwf hrel hinv hq
      cases r with
      | Err e =>
        have hrun' : (ok (core.result.Result.Err e, st1) : Result _) = ok o := hrun
        have ho := Result.ok_injective hrun'
        subst ho
        refine ⟨AOut₀.err ?_, hF⟩
        simp only [absNameLFrom, List.drop_eq_getElem_cons hlt, hnm, List.map_cons,
          Frontend.internNameList, am_run_bind']
        exact AErrSim.bind (AErrSim.bind (Sim₀.apply_err hS) _) _
      | Ok h =>
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS
        obtain ⟨hS2, hF2⟩ := ih (ns.val.length - i2.val) (by omega) (out := out1)
          rfl hrel1 hinv1 hwf hrun
        refine ⟨?_, hF.trans hF2⟩
        have hstep : (do pure (absNIdxL out ++
              (← Frontend.internNameList (absNameLFrom ns i))) : AM (List NIdx)).run lst
            = (do pure (absNIdxL out1 ++
              (← Frontend.internNameList (absNameLFrom ns i2))) : AM (List NIdx)).run lst1 := by
          simp only [absNameLFrom, List.drop_eq_getElem_cons hlt, hnm, List.map_cons,
            Frontend.internNameList, hi2v, bind_assoc, pure_bind]
          rw [run_bind_ok hx1]
          simp only [absNIdxL, ConRon.Refine.vec_push_val hout1, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
            List.nil_append]
        show AOut₀ _ _ _ _ _
        rw [hstep]
        exact hS2

/-- `intern_name_list_go` ⊑ `Frontend.internNameList` at the cursor.

**Restated by task #97-P5-Top: the old statement was false.**  The port's
walk ACCUMULATES — it returns `out` with the new handles pushed on — so its
result abstracts by `absNIdxL` alone; the old `fun v => absNIdxL out ++
absNIdxL v` counted `out` twice and failed at every call with a nonempty
accumulator. -/
theorem intern_name_list_go_refines {pers st lst}
    {ns : alloc.vec.Vec kernel.name.Name} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : NamesWF ns)
    (hrun : arena.intern.intern_name_list_go pers st ns i out = ok o) :
    Sim₀ absNIdxL pers lst o
      (do pure (absNIdxL out ++ (← Frontend.internNameList (absNameLFrom ns i)))) :=
  (intern_name_list_go_aux _ rfl hrel hinv hwf hrun).1

/-- `intern_name_list` ⊑ `Frontend.internNameList`. -/
theorem intern_name_list_refines {pers st lst}
    {ns : alloc.vec.Vec kernel.name.Name} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : NamesWF ns)
    (hrun : arena.intern.intern_name_list pers st ns = ok o) :
    Sim₀ absNIdxL pers lst o
      (Frontend.internNameList (ConRon.Refine.absNames ns)) := by
  rw [arena.intern.intern_name_list] at hrun
  have h := (intern_name_list_go_aux _ rfl hrel hinv hwf hrun).1
  have h0 : absNIdxL (alloc.vec.Vec.new arena.handle.NIdx) = [] := rfl
  have h1 : absNameLFrom ns 0#usize = ConRon.Refine.absNames ns := by
    simp [absNameLFrom, ConRon.Refine.absNames]
  simp only [h0, h1, List.nil_append] at h
  simpa using h

/-- The name-list walk moves no tier flag. -/
theorem intern_name_list_flags {pers st lst}
    {ns : alloc.vec.Vec kernel.name.Name} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : NamesWF ns)
    (hrun : arena.intern.intern_name_list pers st ns = ok o) :
    FlagsEq st.store o.2.store := by
  rw [arena.intern.intern_name_list] at hrun
  exact (intern_name_list_go_aux _ rfl hrel hinv hwf hrun).2

private theorem intern_level_list_go_aux (n : Nat) :
    ∀ {pers st lst} {us : alloc.vec.Vec kernel.level.Level} {i : Std.Usize}
      {out : alloc.vec.Vec arena.handle.LIdx} {o},
      us.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LevelsWF us →
      arena.intern.intern_level_list_go pers st us i out = ok o →
      Sim₀ absLIdxL pers lst o
        (do pure (absLIdxL out ++ (← internLevelList (absLevelLFrom us i)))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst us i out o hn hrel hinv hwf hrun
    rw [arena.intern.intern_level_list_go.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i hge
      have hlen : us.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val us; scalar_tac
      have ho := Result.ok_injective hrun
      subst ho
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      simp [absLevelLFrom, List.drop_eq_nil_of_le hlen, internLevelList]
      rfl
    · rename_i hge
      have hlt : i.val < us.val.length := by
        have := alloc.vec.Vec.len_val us; scalar_tac
      obtain ⟨u, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hu : us.val[i.val] = u := by
        have hg := vec_index_getElem?' hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have huwf : ConRon.Refine.LevelWF u := hwf u (hu ▸ List.getElem_mem hlt)
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := q
      have hS := intern_level_run₀ hrel hinv huwf hq
      cases r with
      | Err e =>
        have hrun' : (ok (core.result.Result.Err e, st1) : Result _) = ok o := hrun
        have ho := Result.ok_injective hrun'
        subst ho
        refine AOut₀.err ?_
        simp only [absLevelLFrom, List.drop_eq_getElem_cons hlt, hu, List.map_cons,
          internLevelList, am_run_bind']
        exact AErrSim.bind (AErrSim.bind (Sim₀.apply_err hS) _) _
      | Ok h =>
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS
        have hS2 := ih (us.val.length - i2.val) (by omega) (out := out1)
          rfl hrel1 hinv1 hwf hrun
        have hstep : (do pure (absLIdxL out ++
              (← internLevelList (absLevelLFrom us i))) : AM (List LIdx)).run lst
            = (do pure (absLIdxL out1 ++
              (← internLevelList (absLevelLFrom us i2))) : AM (List LIdx)).run lst1 := by
          simp only [absLevelLFrom, List.drop_eq_getElem_cons hlt, hu, List.map_cons,
            internLevelList, hi2v, bind_assoc, pure_bind]
          rw [run_bind_ok hx1]
          simp only [absLIdxL, ConRon.Refine.vec_push_val hout1, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
            List.nil_append]
        show AOut₀ _ _ _ _ _
        rw [hstep]
        exact hS2

/-- `intern_level_list_go` ⊑ `Arena.internLevelList` at the cursor.
**Restated by task #97-P5-Top** (the result abstracts by `absLIdxL` alone:
the walk accumulates into `out`; see `intern_name_list_go_refines`). -/
theorem intern_level_list_go_refines {pers st lst}
    {us : alloc.vec.Vec kernel.level.Level} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : LevelsWF us)
    (hrun : arena.intern.intern_level_list_go pers st us i out = ok o) :
    Sim₀ absLIdxL pers lst o
      (do pure (absLIdxL out ++ (← internLevelList (absLevelLFrom us i)))) :=
  intern_level_list_go_aux _ rfl hrel hinv hwf hrun

/-! ### The callees in the judgement shapes -/

open Lockstep in
private theorem intern_name_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ns : alloc.vec.Vec kernel.name.Name) (hwf : NamesWF ns) :
    LS pers (fun a b => b = a.val.map absNIdx) (arena.intern.intern_name_list pers st ns) lst
      (Frontend.internNameList (ConRon.Refine.absNames ns)) :=
  LS.ofSim₀ fun _ h => intern_name_list_refines hrel hinv hwf h

open Lockstep in
/-- The level list at a fresh cursor, against `internLevelList` itself. -/
private theorem intern_level_list0_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (us : alloc.vec.Vec kernel.level.Level) (hwf : LevelsWF us) :
    LS pers (fun a b => b = absLIdxL a)
      (arena.intern.intern_level_list_go pers st us 0#usize (alloc.vec.Vec.new _)) lst
      (internLevelList (ConRon.Refine.absLevels us)) := by
  refine LS.ofSim₀ fun _ h => ?_
  have := intern_level_list_go_refines hrel hinv hwf h
  simpa [absLevelLFrom, ConRon.Refine.absLevels, absLIdxL, alloc.vec.Vec.new] using this

open Lockstep in
/-- The expression list at a fresh cursor, against `internExprList` itself. -/
private theorem intern_expr_list0_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : EMemoRel rm lm) (es : alloc.vec.Vec kernel.expr.Expr)
    (hwf : ExprsWF es) :
    LSM pers (fun a b => b = a.val.map absEIdx)
      (arena.intern.intern_expr_list_go pers st rm es 0#usize (alloc.vec.Vec.new _)) lst
      (Frontend.internExprList lm (ConRon.Refine.absExprs es)) := by
  have h := intern_expr_list_go_ls (i := 0#usize) (out := alloc.vec.Vec.new _) hrel hinv hm hwf
  rw [internExprList_pmapFrom] at h
  refine LSM.twin_eq h ?_
  simp [ConRon.Refine.absExprs, alloc.vec.Vec.new]

/-! ### `ConstantVal`, the rule and its firing mode -/

section decl
attribute [local simp] absIConstantVal absIRecRuleFire absIRecRule absIIndCaps absIProjTable
  absIConstantInfo absIDeclaration ConRon.Refine.absConstantVal ConRon.Refine.absFire
  ConRon.Refine.absRecRule ConRon.Refine.absIndCaps ConRon.Refine.absProjTable
  ConRon.Refine.absConstantInfo ConRon.Refine.absDeclaration

open Lockstep in
/-- `intern_cv_go` ⊑ `Frontend.internCV`, in the judgement shape. -/
theorem intern_cv_go_ls {pers st lst rm lm} {cv : kernel.env.ConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantValWF cv) :
    LSM pers (fun a b => b = absIConstantVal a) (arena.intern.intern_cv_go pers st rm cv) lst
      (Frontend.internCV lm (ConRon.Refine.absConstantVal cv)) := by
  obtain ⟨hn, hlps, hty⟩ := hwf
  rw [arena.intern.intern_cv_go]
  simp only [Frontend.internCV, ConRon.Refine.absConstantVal]
  refine LSM.bindS (intern_name_ls' hrel hinv _ hn) (by lsm_err) ?_
  intro a b st1 lst1 hR hrel1 hinv1
  subst hR
  refine LSM.bindS (intern_name_list_ls hrel1 hinv1 _ hlps) (by lsm_err) ?_
  intro a2 b2 st2 lst2 hR2 hrel2 hinv2
  subst hR2
  refine LSM.bindM (intern_expr_go_ls hrel2 hinv2 hm hty) (by lsm_err) ?_
  intro a3 b3 s3 st3 m3 lst3 hms3 hR3 hrel3 hinv3
  subst hR3
  exact LSM.pure hms3 rfl hrel3 hinv3

/-- `intern_cv_go` ⊑ `Frontend.internCV`. -/
theorem intern_cv_go_refines {pers st lst rm lm} {cv : kernel.env.ConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantValWF cv)
    (hrun : arena.intern.intern_cv_go pers st rm cv = ok o) :
    SimEM absIConstantVal pers lst o
      (Frontend.internCV lm (ConRon.Refine.absConstantVal cv)) :=
  Lockstep.LSM.toSimEM (intern_cv_go_ls hrel hinv hm hwf) hrun

/-- `intern_cv` ⊑ `Arena.internCV`. -/
theorem intern_cv_refines {pers st lst} {cv : kernel.env.ConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantValWF cv)
    (hrun : arena.intern.intern_cv pers st cv = ok o) :
    Sim₀ absIConstantVal pers lst o
      (internCV (ConRon.Refine.absConstantVal cv)) := by
  rw [arena.intern.intern_cv] at hrun
  exact Lockstep.LS.toSim₀
    (Lockstep.LSM.fresh fun rm hm => intern_cv_go_ls hrel hinv hm hwf) hrun

open Lockstep in
/-- `intern_fire` ⊑ `Frontend.internFire`, in the judgement shape. -/
theorem intern_fire_ls {pers st lst rm lm} {f : kernel.env.RecRuleFire}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleFireWF f) :
    LSM pers (fun a b => b = absIRecRuleFire a) (arena.intern.intern_fire pers st rm f) lst
      (Frontend.internFire lm (ConRon.Refine.absFire f)) := by
  cases f with
  | Inert =>
    rw [arena.intern.intern_fire]; simp only [Frontend.internFire, ConRon.Refine.absFire]
    exact LSM.pure hm rfl hrel hinv
  | Plain =>
    rw [arena.intern.intern_fire]; simp only [Frontend.internFire, ConRon.Refine.absFire]
    exact LSM.pure hm rfl hrel hinv
  | Nested lvls pins =>
    obtain ⟨hl, hp⟩ := hwf
    rw [arena.intern.intern_fire]; simp only [Frontend.internFire, ConRon.Refine.absFire]
    refine LSM.bindS (intern_level_list0_ls hrel hinv lvls hl) (by lsm_err) ?_
    intro a b st1 lst1 hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_list0_ls hrel1 hinv1 hm pins hp) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms2 rfl hrel2 hinv2

/-- `intern_fire` ⊑ `Frontend.internFire`. -/
theorem intern_fire_refines {pers st lst rm lm} {f : kernel.env.RecRuleFire} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleFireWF f)
    (hrun : arena.intern.intern_fire pers st rm f = ok o) :
    SimEM absIRecRuleFire pers lst o
      (Frontend.internFire lm (ConRon.Refine.absFire f)) :=
  Lockstep.LSM.toSimEM (intern_fire_ls hrel hinv hm hwf) hrun

open Lockstep in
/-- `intern_rule` ⊑ `Frontend.internRule`, in the judgement shape. -/
theorem intern_rule_ls {pers st lst rm lm} {rl : kernel.env.RecRule}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleWF rl) :
    LSM pers (fun a b => b = absIRecRule a) (arena.intern.intern_rule pers st rm rl) lst
      (Frontend.internRule lm (ConRon.Refine.absRecRule rl)) := by
  obtain ⟨hc, hf, hr⟩ := hwf
  rw [arena.intern.intern_rule]
  simp only [Frontend.internRule, ConRon.Refine.absRecRule]
  refine LSM.bindS (intern_name_ls' hrel hinv _ hc) (by lsm_err) ?_
  intro a b st1 lst1 hR hrel1 hinv1
  subst hR
  refine LSM.bindM (intern_fire_ls hrel1 hinv1 hm hf) (by lsm_err) ?_
  intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
  subst hR2
  refine LSM.bindM (intern_expr_go_ls hrel2 hinv2 hms2 hr) (by lsm_err) ?_
  intro a3 b3 s3 st3 m3 lst3 hms3 hR3 hrel3 hinv3
  subst hR3
  exact LSM.pure hms3 rfl hrel3 hinv3

/-- `intern_rule` ⊑ `Frontend.internRule`. -/
theorem intern_rule_refines {pers st lst rm lm} {rl : kernel.env.RecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleWF rl)
    (hrun : arena.intern.intern_rule pers st rm rl = ok o) :
    SimEM absIRecRule pers lst o
      (Frontend.internRule lm (ConRon.Refine.absRecRule rl)) :=
  Lockstep.LSM.toSimEM (intern_rule_ls hrel hinv hm hwf) hrun

open Lockstep in
private theorem intern_rules_aux (n : Nat) :
    ∀ {pers st lst rm lm} (es : alloc.vec.Vec kernel.env.RecRule) (i : Std.Usize)
      (out : alloc.vec.Vec arena.env.IRecRule),
      es.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      EMemoRel rm lm → (∀ x ∈ es.val, RecRuleWF x) →
      LSM pers (fun a b => b = a.val.map absIRecRule)
        (arena.intern.intern_rules pers st rm es i out) lst
        (pmapFrom Frontend.internRule lm (out.val.map absIRecRule) ((es.val.drop i.val).map ConRon.Refine.absRecRule)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    rw [arena.intern.intern_rules, vecFrom_nil v _ i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_pos (by scalar_tac)]
    exact LSM.pure hm rfl hrel hinv
  | succ k ih =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    have hlt : i.val < v.val.length := by omega
    rw [arena.intern.intern_rules, vecFrom_cons v _ i hlt, pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_neg (by scalar_tac)]
    refine LSM.bindP fun x hx => ?_
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    subst hxv
    refine LSM.bindM (intern_rule_ls hrel hinv hm (hP _ (List.getElem_mem hlt)))
      (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindP fun out1 hout1 => ?_
    refine LSM.bindP fun i2 hi2 => ?_
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have h := ih v i2 out1 (by omega) hrel1 hinv1 hms hP
    rw [ConRon.Refine.vec_push_val hout1, hi2v] at h
    simpa [List.map_append] using h

theorem internRules_pmapFrom (m : Frontend.EMemo) l acc :
    pmapFrom Frontend.internRule m acc l =
      (do let (m, ys) ← Frontend.internRules m l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ Frontend.internRules (fun _ => rfl) (fun _ _ _ => rfl) l m acc


open Lockstep in
private theorem intern_rules0_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : EMemoRel rm lm) (rs : alloc.vec.Vec kernel.env.RecRule)
    (hwf : RecRulesWF rs) :
    LSM pers (fun a b => b = a.val.map absIRecRule)
      (arena.intern.intern_rules pers st rm rs 0#usize (alloc.vec.Vec.new _)) lst
      (Frontend.internRules lm (rs.val.map ConRon.Refine.absRecRule)) := by
  have h := intern_rules_aux _ rs 0#usize (alloc.vec.Vec.new _) rfl hrel hinv hm hwf
  rw [internRules_pmapFrom] at h
  refine LSM.twin_eq h ?_
  simp [alloc.vec.Vec.new]

/-- `intern_rules` ⊑ `Frontend.internRules` at the cursor. -/
theorem intern_rules_refines {pers st lst rm lm}
    {rs : alloc.vec.Vec kernel.env.RecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRulesWF rs)
    (hrun : arena.intern.intern_rules pers st rm rs i out = ok o) :
    SimEM absIRecRuleL pers lst o
      (do let (m, hs) ← Frontend.internRules lm (absRecRuleLFrom rs i)
          pure (m, absIRecRuleL out ++ hs)) := by
  have h := intern_rules_aux _ rs i out rfl hrel hinv hm hwf
  rw [internRules_pmapFrom] at h
  exact Lockstep.LSM.toSimEM h hrun

open Lockstep in
private theorem intern_caps_ls {pers st lst} {c : kernel.env.IndCaps}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hwf : IndCapsWF c) :
    LS pers (fun a b => b = absIIndCaps a) (arena.intern.intern_caps pers st c) lst
      (Frontend.internCaps (ConRon.Refine.absIndCaps c)) := by
  obtain ⟨hn, -⟩ := hwf
  rw [arena.intern.intern_caps]
  simp only [Frontend.internCaps, ConRon.Refine.absIndCaps]
  refine LS.bind (intern_name_ls' hrel hinv _ hn) rfl (fun _ _ => errArm_ok) ?_
  intro a b st1 lst1 hR hrel1 hinv1
  subst hR
  refine LS.bind_eq fun pw hpw => ?_
  rw [ConRon.Refine.PropWhen.dup_eq hpw]
  exact LS.pure rfl hrel1 hinv1

/-- `intern_caps` ⊑ `Frontend.internCaps` — no memo: an `IndCaps` holds one
name and no term. -/
theorem intern_caps_refines {pers st lst} {c : kernel.env.IndCaps} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hwf : IndCapsWF c)
    (hrun : arena.intern.intern_caps pers st c = ok o) :
    Sim₀ absIIndCaps pers lst o
      (Frontend.internCaps (ConRon.Refine.absIndCaps c)) :=
  Lockstep.LS.toSim₀ (intern_caps_ls hrel hinv hwf) hrun

/-! ### The projection table

`intern_proj_table` interns the structure's name, builds the reserved table
name at the STORE level (`arena::env::proj_table_name`, the twin's
`projTableName`), and hands the rest to `intern_proj_table_rest` (extraction
rule 5), whose twin is `internProjTableRest`, `internProjTable` past those two
handles.  (The old statement of `intern_proj_table_rest_refines` was against
the WHOLE `internProjTable`, which re-interns the structure name: false at a
`sn` that is not its handle.) -/

/-- The `"projTable"` component of the reserved table name. -/
theorem proj_table_s_abs {v : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points (Array.to_slice arena.env.proj_table_name.S) = ok v) :
    ConRon.Refine.absString v = "projTable" ∧ ConRon.Refine.StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32, 84#u32, 97#u32,
      98#u32, 108#u32, 101#u32] := by
    rw [ConRon.Refine.Env.code_points_val h, Array.val_to_slice, arena.env.proj_table_name.S,
      Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

open Lockstep in
/-- `arena::env::proj_table_name` ⊑ `projTableName` — two name interns at the
store level. -/
theorem proj_table_name_lss {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (sn : arena.handle.NIdx) :
    LSS pers (fun a b => b = absNIdx a) (arena.env.proj_table_name pers st.store sn) st lst
      (projTableName (absNIdx sn)) := by
  intro o s' hrun
  rw [arena.env.proj_table_name] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [dupId_nidx _ _ hn] at hrun
  obtain ⟨sl, hsl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [lift, Result.ok.injEq] at hsl
  subst hsl
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨habs, hswf⟩ := proj_table_s_abs hv
  obtain ⟨⟨r1, ar1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hok1, herr1, -⟩ :=
    estore_intern_name_abs (ls := lst.store) hrel.store hinv.store
      (v := arena.store.NNodeView.Str sn v) hswf h1
  have hrun1 : (projTableName (absNIdx sn)).run lst
      = ((internNNode (.str (absNIdx sn) "projTable")) >>= fun s =>
          internNNode (.num s 0)).run lst := rfl
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    simp only [Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact AErrSim.of_none (herr1 e rfl)
  | Ok s1 =>
    obtain ⟨hs1, hrelS, hinvS, hcap1⟩ := hok1 s1 rfl
    simp only [absNNodeView, habs] at hs1 hrelS hcap1
    obtain ⟨hok2, herr2, -⟩ :=
      estore_intern_name_abs (ls := (lst.store.internName (.str (absNIdx sn) "projTable")).1)
        hrelS hinvS (v := arena.store.NNodeView.Num s1 0#u64) trivial hrun
    rw [hrun1, run_bind_ok (internNNode_run_of_cap hcap1)]
    cases o with
    | Err e => exact AErrSim.of_none (herr2 e rfl)
    | Ok a =>
      obtain ⟨hs2, hrelS2, hinvS2, hcap2⟩ := hok2 a rfl
      simp only [absNNodeView, hs1, absU, Lockstep.u64_zero_val] at hs2 hrelS2 hcap2
      exact ⟨_, _, internNNode_run_of_cap hcap2, hs2.symm,
        ⟨hrelS2, hrel.memos, hrel.caches, hrel.pins⟩, ⟨hinvS2, hinv.memos, hinv.caches⟩⟩

open Lockstep in
theorem LSM.bindSS {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {st : arena.monad.AState}
    {k : core.result.Result α kernel.core_types.CheckError × arena.store.EStore →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState ×
        ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)}
    {lst : AState} {x : AM β} {g : β → AM (Frontend.EMemo × δ)}
    (hf : LSS pers R₁ f st lst x)
    (he : ∀ e s' o st' mm, k (.Err e, s') = ok (o, st', mm) → o = .Err e)
    (hk : ∀ a b s' lst1, R₁ a b → AStateRel₀ pers { st with store := s' } lst1 →
      AStateInv pers { st with store := s' } → LSM pers R (k (.Ok a, s')) lst1 (g b)) :
    LSM pers R (f >>= k) lst (x >>= g) := by
  intro o st' mm hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r s1 hf1
  cases r with
  | Err e =>
    have := he e s1 o st' mm hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b s1 lst1 hR hrel hinv o st' mm hk1

/-- The twin's `internProjTable` past the structure name and the table name:
`intern_proj_table_rest`'s twin. -/
def internProjTableRest (m : Frontend.EMemo) (t : ConLeche.ProjTable) (sn tn : NIdx) :
    AM (Frontend.EMemo × IProjTable) := do
  let lps ← Frontend.internNameList t.levelParams
  let c ← internName t.ctor
  let ss ← internLevel t.structSort
  let (m, bs) ← Frontend.internExprList m t.bodies.toList
  let gs ← internLevelList t.guards
  pure (m, ⟨sn, tn, lps, t.numParams, c, t.numFields, ss, bs.toArray, gs, t.off⟩)

theorem internProjTable_rest (m : Frontend.EMemo) (t : ConLeche.ProjTable) :
    Frontend.internProjTable m t = (do
      let sn ← internName t.structName
      let tn ← projTableName sn
      internProjTableRest m t sn tn) := rfl

open Lockstep in
private theorem intern_proj_table_rest_ls {pers st lst rm lm} {t : kernel.env.ProjTable}
    {sn tn : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t) :
    LSM pers (fun a b => b = absIProjTable a)
      (arena.intern.intern_proj_table_rest pers st rm t sn tn) lst
      (internProjTableRest lm (ConRon.Refine.absProjTable t) (absNIdx sn) (absNIdx tn)) := by
  obtain ⟨-, hlps, hc, hss, hbs, hgs⟩ := hwf
  rw [arena.intern.intern_proj_table_rest]
  simp only [internProjTableRest, ConRon.Refine.absProjTable]
  refine LSM.bindS (intern_name_list_ls hrel hinv _ hlps) (by lsm_err) ?_
  intro a1 b1 st1 lst1 hR1 hrel1 hinv1
  subst hR1
  refine LSM.bindS (intern_name_ls' hrel1 hinv1 _ hc) (by lsm_err) ?_
  intro a2 b2 st2 lst2 hR2 hrel2 hinv2
  subst hR2
  refine LSM.bindS (intern_level_ls' hrel2 hinv2 _ hss) (by lsm_err) ?_
  intro a3 b3 st3 lst3 hR3 hrel3 hinv3
  subst hR3
  refine LSM.bindM (intern_expr_list0_ls hrel3 hinv3 hm _ hbs) (by lsm_err) ?_
  intro a4 b4 s4 st4 m4 lst4 hms4 hR4 hrel4 hinv4
  subst hR4
  refine LSM.bindS (intern_level_list0_ls hrel4 hinv4 _ hgs) (by lsm_err) ?_
  intro a5 b5 st5 lst5 hR5 hrel5 hinv5
  subst hR5
  exact LSM.pure hms4 rfl hrel5 hinv5

/-- `intern_proj_table_rest` is the Rust-only tail of `intern_proj_table` past
its two name interns (extraction rule 5), stated against the twin's tail with
those two handles in hand (`internProjTableRest`). -/
theorem intern_proj_table_rest_refines {pers st lst rm lm}
    {t : kernel.env.ProjTable} {sn tn : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t)
    (hrun : arena.intern.intern_proj_table_rest pers st rm t sn tn = ok o) :
    SimEM absIProjTable pers lst o
      (internProjTableRest lm (ConRon.Refine.absProjTable t) (absNIdx sn) (absNIdx tn)) :=
  Lockstep.LSM.toSimEM (intern_proj_table_rest_ls hrel hinv hm hwf) hrun

open Lockstep in
private theorem intern_proj_table_ls {pers st lst rm lm} {t : kernel.env.ProjTable}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t) :
    LSM pers (fun a b => b = absIProjTable a)
      (arena.intern.intern_proj_table pers st rm t) lst
      (Frontend.internProjTable lm (ConRon.Refine.absProjTable t)) := by
  rw [arena.intern.intern_proj_table, internProjTable_rest]
  refine LSM.bindS (intern_name_ls' hrel hinv _ hwf.1) (by lsm_err) ?_
  intro a1 b1 st1 lst1 hR1 hrel1 hinv1
  subst hR1
  refine LSM.bindSS (proj_table_name_lss hrel1 hinv1 a1) (by lsm_err) ?_
  intro a2 b2 s2 lst2 hR2 hrel2 hinv2
  subst hR2
  exact intern_proj_table_rest_ls hrel2 hinv2 hm hwf

/-- `intern_proj_table` ⊑ `Frontend.internProjTable`. -/
theorem intern_proj_table_refines {pers st lst rm lm}
    {t : kernel.env.ProjTable} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t)
    (hrun : arena.intern.intern_proj_table pers st rm t = ok o) :
    SimEM absIProjTable pers lst o
      (Frontend.internProjTable lm (ConRon.Refine.absProjTable t)) :=
  Lockstep.LSM.toSimEM (intern_proj_table_ls hrel hinv hm hwf) hrun

/-! ### The stored constant and the declaration -/

open Lockstep in
/-- `intern_ci_go` ⊑ `Frontend.internCI`, in the judgement shape. -/
theorem intern_ci_go_ls {pers st lst rm lm} {c : kernel.env.ConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantInfoWF c) :
    LSM pers (fun a b => b = absIConstantInfo a) (arena.intern.intern_ci_go pers st rm c) lst
      (Frontend.internCI lm (ConRon.Refine.absConstantInfo c)) := by
  cases c with
  | AxiomInfo v =>
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    exact LSM.pure hms rfl hrel1 hinv1
  | DefnInfo v e h =>
    obtain ⟨hv, he⟩ := hwf
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_go_ls hrel1 hinv1 hms he) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    refine LSM.bindP fun rh hrh => ?_
    rw [Lockstep.rhint_dup_spec h rh hrh]
    exact LSM.pure hms2 rfl hrel2 hinv2
  | ThmInfo v e =>
    obtain ⟨hv, he⟩ := hwf
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_go_ls hrel1 hinv1 hms he) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms2 rfl hrel2 hinv2
  | IndInfo v c2 =>
    obtain ⟨hv, hc⟩ := hwf
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindS (intern_caps_ls hrel1 hinv1 hc) (by lsm_err) ?_
    intro a2 b2 st2 lst2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms rfl hrel2 hinv2
  | CtorInfo v np nf =>
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    exact LSM.pure hms rfl hrel1 hinv1
  | RecInfo v mi rp rs =>
    obtain ⟨hv, hrs⟩ := hwf
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_rules0_ls hrel1 hinv1 hms rs hrs) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms2 rfl hrel2 hinv2
  | ProjInfo t =>
    rw [arena.intern.intern_ci_go]; simp only [Frontend.internCI, ConRon.Refine.absConstantInfo]
    refine LSM.bindM (intern_proj_table_ls hrel hinv hm hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    exact LSM.pure hms rfl hrel1 hinv1

/-- `intern_ci_go` ⊑ `Frontend.internCI` — the seven `ConstantInfo`
constructors. -/
theorem intern_ci_go_refines {pers st lst rm lm} {c : kernel.env.ConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantInfoWF c)
    (hrun : arena.intern.intern_ci_go pers st rm c = ok o) :
    SimEM absIConstantInfo pers lst o
      (Frontend.internCI lm (ConRon.Refine.absConstantInfo c)) :=
  Lockstep.LSM.toSimEM (intern_ci_go_ls hrel hinv hm hwf) hrun

/-- `intern_ci` ⊑ `Arena.internCI`. -/
theorem intern_ci_refines {pers st lst} {c : kernel.env.ConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantInfoWF c)
    (hrun : arena.intern.intern_ci pers st c = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (internCI (ConRon.Refine.absConstantInfo c)) := by
  rw [arena.intern.intern_ci] at hrun
  exact Lockstep.LS.toSim₀
    (Lockstep.LSM.fresh fun rm hm => intern_ci_go_ls hrel hinv hm hwf) hrun

open Lockstep in
private theorem intern_ci_list_go_aux (n : Nat) :
    ∀ {pers st lst rm lm} (es : alloc.vec.Vec kernel.env.ConstantInfo) (i : Std.Usize)
      (out : alloc.vec.Vec arena.env.IConstantInfo),
      es.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      EMemoRel rm lm → (∀ x ∈ es.val, ConstantInfoWF x) →
      LSM pers (fun a b => b = a.val.map absIConstantInfo)
        (arena.intern.intern_ci_list_go pers st rm es i out) lst
        (pmapFrom Frontend.internCI lm (out.val.map absIConstantInfo) ((es.val.drop i.val).map ConRon.Refine.absConstantInfo)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    rw [arena.intern.intern_ci_list_go, vecFrom_nil v _ i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_pos (by scalar_tac)]
    exact LSM.pure hm rfl hrel hinv
  | succ k ih =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    have hlt : i.val < v.val.length := by omega
    rw [arena.intern.intern_ci_list_go, vecFrom_cons v _ i hlt, pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_neg (by scalar_tac)]
    refine LSM.bindP fun x hx => ?_
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    subst hxv
    refine LSM.bindM (intern_ci_go_ls hrel hinv hm (hP _ (List.getElem_mem hlt)))
      (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindP fun out1 hout1 => ?_
    refine LSM.bindP fun i2 hi2 => ?_
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have h := ih v i2 out1 (by omega) hrel1 hinv1 hms hP
    rw [ConRon.Refine.vec_push_val hout1, hi2v] at h
    simpa [List.map_append] using h

theorem internCIList_pmapFrom (m : Frontend.EMemo) l acc :
    pmapFrom Frontend.internCI m acc l =
      (do let (m, ys) ← Frontend.internCIList m l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ Frontend.internCIList (fun _ => rfl) (fun _ _ _ => rfl) l m acc


/-- `intern_ci_list_go` ⊑ `Frontend.internCIList` at the cursor. -/
theorem intern_ci_list_go_refines {pers st lst rm lm}
    {cs : alloc.vec.Vec kernel.env.ConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantInfosWF cs)
    (hrun : arena.intern.intern_ci_list_go pers st rm cs i out = ok o) :
    SimEM absICIL pers lst o
      (do let (m, hs) ← Frontend.internCIList lm (absCIListFrom cs i)
          pure (m, absICIL out ++ hs)) := by
  have h := intern_ci_list_go_aux _ cs i out rfl hrel hinv hm hwf
  rw [internCIList_pmapFrom] at h
  exact Lockstep.LSM.toSimEM h hrun

open Lockstep in
private theorem intern_ci_list0_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : EMemoRel rm lm) (cs : alloc.vec.Vec kernel.env.ConstantInfo)
    (hwf : ConstantInfosWF cs) :
    LSM pers (fun a b => b = a.val.map absIConstantInfo)
      (arena.intern.intern_ci_list_go pers st rm cs 0#usize (alloc.vec.Vec.new _)) lst
      (Frontend.internCIList lm (ConRon.Refine.absConstantInfos cs)) := by
  have h := intern_ci_list_go_aux _ cs 0#usize (alloc.vec.Vec.new _) rfl hrel hinv hm hwf
  rw [internCIList_pmapFrom] at h
  refine LSM.twin_eq h ?_
  simp [ConRon.Refine.absConstantInfos, alloc.vec.Vec.new]

/-- `intern_ci_list` ⊑ `Arena.internCIList` — the block at ONE memo, so that
the sharing between a block's members survives. -/
theorem intern_ci_list_refines {pers st lst}
    {cs : alloc.vec.Vec kernel.env.ConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantInfosWF cs)
    (hrun : arena.intern.intern_ci_list pers st cs = ok o) :
    Sim₀ absICIL pers lst o
      (internCIList (ConRon.Refine.absConstantInfos cs)) := by
  rw [arena.intern.intern_ci_list] at hrun
  exact Lockstep.LS.toSim₀
    (Lockstep.LSM.fresh fun rm hm => intern_ci_list0_ls hrel hinv hm cs hwf) hrun

open Lockstep in
/-- `intern_decl` ⊑ `Frontend.internDecl`, in the judgement shape. -/
theorem intern_decl_ls {pers st lst rm lm} {d : kernel.env.Declaration}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : DeclarationWF d) :
    LSM pers (fun a b => b = absIDeclaration a) (arena.intern.intern_decl pers st rm d) lst
      (Frontend.internDecl lm (ConRon.Refine.absDeclaration d)) := by
  cases d with
  | AxiomDecl v =>
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    exact LSM.pure hms rfl hrel1 hinv1
  | DefnDecl v e h =>
    obtain ⟨hv, he⟩ := hwf
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_go_ls hrel1 hinv1 hms he) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    refine LSM.bindP fun rh hrh => ?_
    rw [Lockstep.rhint_dup_spec h rh hrh]
    exact LSM.pure hms2 rfl hrel2 hinv2
  | ThmDecl v e =>
    obtain ⟨hv, he⟩ := hwf
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_go_ls hrel1 hinv1 hms he) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms2 rfl hrel2 hinv2
  | OpaqueDecl v e =>
    obtain ⟨hv, he⟩ := hwf
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hv) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindM (intern_expr_go_ls hrel1 hinv1 hms he) (by lsm_err) ?_
    intro a2 b2 s2 st2 m2 lst2 hms2 hR2 hrel2 hinv2
    subst hR2
    exact LSM.pure hms2 rfl hrel2 hinv2
  | BasisDecl k =>
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindP fun bk hbk => ?_
    rw [Lockstep.basis_kind_dup_spec k bk hbk]
    exact LSM.pure hm rfl hrel hinv
  | IndDecl block np =>
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_ci_list0_ls hrel hinv hm block hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    exact LSM.pure hms rfl hrel1 hinv1
  | QuotDecl k v =>
    rw [arena.intern.intern_decl]; simp only [Frontend.internDecl, ConRon.Refine.absDeclaration]
    refine LSM.bindM (intern_cv_go_ls hrel hinv hm hwf) (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindP fun qk hqk => ?_
    rw [Lockstep.quot_kind_dup_spec k qk hqk]
    exact LSM.pure hms rfl hrel1 hinv1

/-- `intern_decl` ⊑ `Frontend.internDecl` — the seven `Declaration`
constructors. -/
theorem intern_decl_refines {pers st lst rm lm} {d : kernel.env.Declaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : DeclarationWF d)
    (hrun : arena.intern.intern_decl pers st rm d = ok o) :
    SimEM absIDeclaration pers lst o
      (Frontend.internDecl lm (ConRon.Refine.absDeclaration d)) :=
  Lockstep.LSM.toSimEM (intern_decl_ls hrel hinv hm hwf) hrun

open Lockstep in
private theorem intern_decls_go_aux (n : Nat) :
    ∀ {pers st lst rm lm} (es : alloc.vec.Vec kernel.env.Declaration) (i : Std.Usize)
      (out : alloc.vec.Vec arena.env.IDeclaration),
      es.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      EMemoRel rm lm → (∀ x ∈ es.val, DeclarationWF x) →
      LSM pers (fun a b => b = a.val.map absIDeclaration)
        (arena.intern.intern_decls_go pers st rm es i out) lst
        (pmapFrom Frontend.internDecl lm (out.val.map absIDeclaration) ((es.val.drop i.val).map ConRon.Refine.absDeclaration)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    rw [arena.intern.intern_decls_go, vecFrom_nil v _ i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_pos (by scalar_tac)]
    exact LSM.pure hm rfl hrel hinv
  | succ k ih =>
    intro pers st lst rm lm v i out hn hrel hinv hm hP
    have hlt : i.val < v.val.length := by omega
    rw [arena.intern.intern_decls_go, vecFrom_cons v _ i hlt, pmapFrom]
    have hl := alloc.vec.Vec.len_val v
    rw [if_neg (by scalar_tac)]
    refine LSM.bindP fun x hx => ?_
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    subst hxv
    refine LSM.bindM (intern_decl_ls hrel hinv hm (hP _ (List.getElem_mem hlt)))
      (by lsm_err) ?_
    intro a b s st1 m1 lst1 hms hR hrel1 hinv1
    subst hR
    refine LSM.bindP fun out1 hout1 => ?_
    refine LSM.bindP fun i2 hi2 => ?_
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have h := ih v i2 out1 (by omega) hrel1 hinv1 hms hP
    rw [ConRon.Refine.vec_push_val hout1, hi2v] at h
    simpa [List.map_append] using h

theorem internDecls_pmapFrom (m : Frontend.EMemo) l acc :
    pmapFrom Frontend.internDecl m acc l =
      (do let (m, ys) ← Frontend.internDecls m l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ Frontend.internDecls (fun _ => rfl) (fun _ _ _ => rfl) l m acc


/-- `intern_decls_go` ⊑ `Frontend.internDecls` at the cursor. -/
theorem intern_decls_go_refines {pers st lst rm lm}
    {ds : alloc.vec.Vec kernel.env.Declaration} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ∀ d ∈ ds.val, DeclarationWF d)
    (hrun : arena.intern.intern_decls_go pers st rm ds i out = ok o) :
    SimEM absIDeclL pers lst o
      (do let (m, hs) ← Frontend.internDecls lm (absDeclLFrom ds i)
          pure (m, absIDeclL out ++ hs)) := by
  have h := intern_decls_go_aux _ ds i out rfl hrel hinv hm hwf
  rw [internDecls_pmapFrom] at h
  exact Lockstep.LSM.toSimEM h hrun

/-- `intern_decls` ⊑ `Frontend.internDecls` at a fresh memo. -/
theorem intern_decls_refines {pers st lst}
    {ds : alloc.vec.Vec kernel.env.Declaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ d ∈ ds.val, DeclarationWF d)
    (hrun : arena.intern.intern_decls pers st ds = ok o) :
    Sim₀ absIDeclL pers lst o
      (do pure (← Frontend.internDecls ∅ (ds.val.map ConRon.Refine.absDeclaration)).2) := by
  rw [arena.intern.intern_decls] at hrun
  refine Lockstep.LS.toSim₀ (Lockstep.LSM.fresh fun rm hm => ?_) hrun
  have h := intern_decls_go_aux _ ds 0#usize (alloc.vec.Vec.new _) rfl hrel hinv hm hwf
  rw [internDecls_pmapFrom] at h
  refine Lockstep.LSM.twin_eq h ?_
  simp [alloc.vec.Vec.new]

end decl

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.memo_empty_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_empty_refines

/-- info: 'ConRon.Refine2.intern_expr_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_expr_refines

/-- info: 'ConRon.Refine2.intern_expr_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_expr_list_refines

/-- info: 'ConRon.Refine2.intern_ci_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_ci_list_refines

/-- info: 'ConRon.Refine2.intern_decls_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_decls_refines

/-- info: 'ConRon.Refine2.intern_proj_table_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_proj_table_refines

end ConRon.Refine2

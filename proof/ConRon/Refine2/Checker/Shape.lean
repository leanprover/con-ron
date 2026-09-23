/-
# `ConRon.Refine2.Checker.Shape` — the three statement shapes the checker tier adds

**Task #97-P5-Checker** (DESIGN.md §8.2, Theorem 2), the shared base of the
`Refine2/Promote/**` and `Refine2/Checker/**` tiers.  `Refine2/Shape.lean`
carries `Sim` / `SimR` / `SimP` / `SimS`, whose success arm abstracts the
result with a **function** `A : α → β`.  The declaration checker has three
results for which no such function exists, and each one needs the abstraction
to be a RELATION instead:

| result | why a function will not do |
|---|---|
| `IFEnv` | `Refine2/AbsState.lean`'s `IFEnvRel` composes the index probe with the array read (task #97-P6-5's lever 1); a `ron::HashMap2` is not recoverable from a `Std.HashMap` |
| `PMemo` | `arena::promote` threads four `HashMap2`s as an argument-and-result pair (task #97-P5-0's **finding 4**, one tier down) |
| `HashMap2<Expr, EIdx>` | `arena::intern`'s memo, the same |

So this file's `SimRel` is `Sim` with `A : α → β` replaced by
`R : α → β → Prop`, and `Sim` is recovered as `SimRel (fun r v => v = A r)` —
which `Sim.toSimRel` proves, so a caller that has the stronger statement feeds
a consumer that wants the weaker one without a second lemma.

**`POut` / `SimPM`** and **`EOut` / `SimEM`** are `SimRel` with the memo
quantified beside the state, one for each of the two memo-threading families;
they are `Refine2/ExprOps/Read.lean`'s `WOut` / `LOut` / `FOut` at another
memo, three lines each, exactly as finding 4 predicted the Core tier would
want them.

## Why the memos are not in `AStateRel`

They are not in the state.  `PMemo::empty` and `memo_empty` are built per
declaration and MOVED through the walk (DESIGN §8.3: "the memo is per
DECLARATION — a scratch handle means nothing once the tier is dropped"), so
each is an ordinary argument and an ordinary result; putting either in
`AState` would have made `AStateRel` false at every call that owns one.
-/
import ConRon.Refine2.Specs
import ConRon.Refine2.ExprOps.Read
import ConRon.Refine2.Core.Bracket
import ConRon.Arena

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun sl_v)

/-! ## Rule 11 — the twin's `do` blocks, reduced (task #97-P5-Checker-2)

Task #97-P5-Checker §6 left the eight `_unfold` equations of
`Refine2/Checker/Spec.lean` and the three of `Refine2/Promote/Promote.lean`
open, saying *"a `do`-block equation in `StateT σ (Except ε)` needs the same
reduction discipline rule 10 names"*.  It needs THREE lemmas, and they are
these.

The obstruction is the `do` elaborator's **join point**.  A twin written

    if c then fail e
    rest

elaborates to `if c then fail e else rest` — the continuation is pushed INTO
the branch — where a transcription that names the guard separately is
`(if c then fail e else pure ()) >>= fun _ => rest`.  `rfl` cannot bridge
that: `StateT`'s `bind` matches on the inner `Except`, so `(a >>= f) >>= g` is
not definitionally `a >>= fun x => f x >>= g` at an opaque `a`.  So the
equation is a `simp only` over

* `bind_assoc` and `pure_bind` — `AM` is a `LawfulMonad`;
* `am_ite_bind` / `am_dite_bind` — push a continuation into an `if`, which is
  what the join point did on the twin's side;
* `am_fail_bind` — a throw swallows its continuation, which is what makes the
  two `if` branches line up.

`twin_reduce [...]` is the four of them plus the caller's own definitions, and
it closes an `_unfold` whose only difference is the grouping.  Where the twin
groups at a `match` rather than an `if` (`Refine2/Promote/Promote.lean`'s
three) the `simp only` is not enough — a matcher with the continuation inlined
is a DIFFERENT constant from the matcher without it — and the recipe is
`split` / `cases` on the discriminant first and `twin_reduce` per arm. -/

/-- A throw swallows its continuation. -/
theorem am_fail_bind {α β : Type} (e : Arena.CheckError) (k : α → AM β) :
    (Arena.fail e >>= k) = Arena.fail e := rfl

/-- A continuation pushes into an `if` — the `do` elaborator's join point,
undone. -/
theorem am_ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : AM α)
    (k : α → AM β) : ((if c then a else b) >>= k) = if c then a >>= k else b >>= k := by
  split <;> rfl

/-- `Except.ok v >>= f = f v` — the step every composed run needs before
`am_run_bind` can see the next bind. -/
theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- **Peel a common `do` prefix.**  `congr 1` on `x >>= f = x >>= g` in `AM`
eta-expands the FUNCTION (`AM α` is `AState → …`) instead of peeling the bind,
which strands the goal at an applied state.  This is the peel that works, and
every `_unfold` whose two sides group at a `match` rather than at an `if`
needs it. -/
theorem am_bind_congr {α β : Type} (x : AM α) {f g : α → AM β}
    (h : ∀ a, f a = g a) : (x >>= f) = (x >>= g) := by
  rw [funext h]

/-- The same at a `dite`. -/
theorem am_dite_bind {α β : Type} (c : Prop) [Decidable c] (a : c → AM α)
    (b : ¬ c → AM α) (k : α → AM β) :
    ((if h : c then a h else b h) >>= k) = if h : c then a h >>= k else b h >>= k := by
  split <;> rfl

/-- **Rule 11.**  Reduce a twin `do` block and its transcription to one
normal form: the caller's own definitions, then the four monadic steps the
join point needs. -/
syntax "twin_reduce" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| twin_reduce [$ts,*]) =>
    `(tactic| simp only [$ts,*, bind_assoc, pure_bind,
        am_fail_bind, am_ite_bind, am_dite_bind])

/-- `twin_reduce` with no extra lemmas. -/
macro "twin_reduce" : tactic =>
  `(tactic| simp only [bind_assoc, pure_bind, am_fail_bind, am_ite_bind, am_dite_bind])

/-! ## `SimRel` — `Sim` with the result RELATED rather than abstracted -/

/-- `AOut` with the result related.  `WF` is gone: a relation says everything
a well-formedness predicate did, and every consumer of this shape in the tier
states its `WF` inside `R`. -/
def AOutRel {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState) (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ v lst', x = .ok (v, lst') ∧ R r v ∧ AStateRel pers st' lst' ∧
      AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- The simulation statement for a Rust function whose result relates rather
than abstracts — `IFEnv` throughout the checker tier. -/
def SimRel {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  AOutRel R pers lst o.1 o.2 (x.run lst)

theorem AOutRel.ok {α β : Type} {R : α → β → Prop} {r : α} {v : β}
    {pers : arena.store.PersTier} {lst lst' : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (hx : x = .ok (v, lst')) (hr : R r v) (hrel : AStateRel pers st' lst')
    (hinv : AStateInv pers st') (hext : Ext lst.store lst'.store) :
    AOutRel R pers lst (.Ok r) st' x := ⟨v, lst', hx, hr, hrel, hinv, hext⟩

theorem AOutRel.err {α β : Type} {R : α → β → Prop}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {lst : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (h : AErrSim e x) :
    AOutRel R pers lst (.Err e) st' x := h

theorem AOutRel.dest {α β : Type} {R : α → β → Prop} {r : α}
    {pers : arena.store.PersTier} {lst : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (h : AOutRel R pers lst (.Ok r) st' x) :
    ∃ v lst', x = .ok (v, lst') ∧ R r v ∧ AStateRel pers st' lst' ∧
      AStateInv pers st' ∧ Ext lst.store lst'.store := h

/-- The value equation is the stronger claim: a `Sim` feeds a `SimRel`
consumer. -/
theorem Sim.toSimRel {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : Sim A (fun _ => True) pers lst o x) :
    SimRel (fun r v => v = A r) pers lst o x := by
  revert h
  unfold Sim SimRel AOut AOutRel
  cases o.1 with
  | Err e => exact id
  | Ok r =>
    rintro ⟨lst', hx, h1, h2, h3, -⟩
    exact ⟨A r, lst', hx, rfl, h1, h2, h3⟩

/-- **The result relation, weakened.**  The fold's statements conclude
`IFEnvRelI` (related AND well formed) because the next step needs both; the
capstone's public conclusion is DESIGN §8.2's `IFEnvRel` alone, and this is
the one step between them. -/
theorem SimRel.mono {α β : Type} {R R' : α → β → Prop}
    {pers : arena.store.PersTier} {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : SimRel R pers lst o x) (hRR : ∀ r v, R r v → R' r v) :
    SimRel R' pers lst o x := by
  revert h
  unfold SimRel AOutRel
  cases o.1 with
  | Err e => exact id
  | Ok r =>
    rintro ⟨v, lst', hx, hr, h1, h2, h3⟩
    exact ⟨v, lst', hx, hRR _ _ hr, h1, h2, h3⟩

/-! ## `SimRE` — a reader that can FAIL

`Refine2/Shape.lean`'s `SimR` is `Result`-valued but never `Err`, which is
what `arena::monad`'s store readers are.  The fifty-eight readers of
`arena::pins` are not: `pin_at` declines with `Internal` when the pin table is
not the expected size, and its signature is `(st : &AState) -> Result<NIdx,
CheckError>` with **no state in the return at all**.  So the shape is `SimR`'s
success arm and `AOut`'s error arm, and it is a fourth shape rather than a
special case of `Sim` because there is no post-state to relate. -/
def SimRE {α β : Type} (A : α → β) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError) (x : AM β) : Prop :=
  match o with
  | .Ok r => x.run lst = .ok (A r, lst)
  | .Err e => AErrSim e (x.run lst)

theorem SimRE.ok {α β : Type} {A : α → β} {lst : AState} {r : α} {x : AM β}
    (h : x.run lst = .ok (A r, lst)) : SimRE A lst (.Ok r) x := h

theorem SimRE.err {α β : Type} {A : α → β} {lst : AState}
    {e : kernel.core_types.CheckError} {x : AM β} (h : AErrSim e (x.run lst)) :
    SimRE A lst (.Err e) x := h

theorem SimRE.apply {α β : Type} {A : α → β} {lst : AState} {r : α} {x : AM β}
    (h : SimRE A lst (.Ok r) x) : x.run lst = .ok (A r, lst) := h

/-- `SimRE` with the result RELATED rather than abstracted: a reader that can
fail and whose answer is an `IFEnv`.  `arena::decl_check::install_basis_decl`
is the one, and it is a reader because a basis install is `fe.push` and
nothing else — only its DECLINE reads the store (for the name in the
message). -/
def SimRelR {α β : Type} (R : α → β → Prop) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError) (x : AM β) : Prop :=
  match o with
  | .Ok r => ∃ v, x.run lst = .ok (v, lst) ∧ R r v
  | .Err e => AErrSim e (x.run lst)

/-! ## The promotion memo (`arena::promote::PMemo`)

Four `RelOn` clauses at `P := True` and four `Inv`s: every key is a bare
handle, so the `Eq2Fwd` dictionaries `Refine2/AbsState.lean` proved
(`eidx_eq2`, `nidx_eq2`, `lidx_eq2`, `lsidx_eq2`) are unrestricted. -/

/-- **`arena::promote::PMemo` against `Arena/Promote.lean`'s.** -/
structure PMemoRel (rm : arena.promote.PMemo) (lm : PMemo) : Prop where
  eM : RelOn (fun _ => True) rm.e_m lm.eM absEIdx absEIdx
  nM : RelOn (fun _ => True) rm.n_m lm.nM absNIdx absNIdx
  lM : RelOn (fun _ => True) rm.l_m lm.lM absLIdx absLIdx
  lsM : RelOn (fun _ => True) rm.ls_m lm.lsM absLsIdx absLsIdx
  eInv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm.e_m
  nInv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rm.n_m
  lInv : Inv arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable rm.l_m
  lsInv : Inv arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable rm.ls_m

/-- **`arena::intern`'s memo**, the one memo of these two tiers keyed on a
con-leche VALUE rather than a handle.  `Refine/Expr.lean`'s `absExpr` is exact
on WELL-FORMED values only (task #97-P5-0's rule 4, and the reason `TblRel` is
`RelOn P` and not `Rel`), so `P` is `ExprWF` and the caller owes it — which
the pin modules discharge from `Refine/Pins*.lean`, every subject of
`arena::intern` being a con-leche pin. -/
def EMemoRel (rm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)
    (lm : Std.HashMap ConLeche.Expr EIdx) : Prop :=
  RelOn ConRon.Refine.ExprWF rm lm ConRon.Refine.absExpr absEIdx ∧
    Inv kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable rm

/-! ## The two memo-threading outcome shapes (finding 4, at this tier) -/

/-- The outcome of a promotion: the twin's answer is `(PMemo × β)`, the memo
related and the value related. -/
def POut {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result (arena.promote.PMemo × α) kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError ((PMemo × β) × AState)) : Prop :=
  match o with
  | .Ok r => ∃ m' v lst', x = .ok ((m', v), lst') ∧ R r.2 v ∧ PMemoRel r.1 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- `POut` at the Rust's outcome pair — the `Sim` of the promotion tier. -/
def SimPM {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result (arena.promote.PMemo × α) kernel.core_types.CheckError ×
      arena.monad.AState)
    (x : AM (PMemo × β)) : Prop :=
  POut R pers lst o.1 o.2 (x.run lst)

/-- The `SimPM` of a promotion whose value abstracts by a FUNCTION — all of
them but `promote_new`. -/
abbrev SimPMF {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result (arena.promote.PMemo × α) kernel.core_types.CheckError ×
      arena.monad.AState)
    (x : AM (PMemo × β)) : Prop :=
  SimPM (fun r v => v = A r) pers lst o x

theorem POut.ok {α β : Type} {R : α → β → Prop} {r : arena.promote.PMemo × α}
    {v : β} {pers : arena.store.PersTier} {lst lst' : AState} {m' : PMemo}
    {st' : arena.monad.AState} {x : Except Arena.CheckError ((PMemo × β) × AState)}
    (hx : x = .ok ((m', v), lst')) (hv : R r.2 v) (hm : PMemoRel r.1 m')
    (hrel : AStateRel pers st' lst') (hinv : AStateInv pers st')
    (hext : Ext lst.store lst'.store) : POut R pers lst (.Ok r) st' x :=
  ⟨m', v, lst', hx, hv, hm, hrel, hinv, hext⟩

theorem POut.err {α β : Type} {R : α → β → Prop} {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lst : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError ((PMemo × β) × AState)} (h : AErrSim e x) :
    POut R pers lst (.Err e) st' x := h

theorem POut.dest {α β : Type} {R : α → β → Prop} {r : arena.promote.PMemo × α}
    {pers : arena.store.PersTier} {lst : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError ((PMemo × β) × AState)}
    (h : POut R pers lst (.Ok r) st' x) :
    ∃ m' v lst', x = .ok ((m', v), lst') ∧ R r.2 v ∧ PMemoRel r.1 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store := h

/-- The outcome of an `arena::intern` walk.  **The memo is outside the
`Result`** on the Rust's side and inside it on the twin's: the port moves the
`HashMap2` back whatever happened, and a thrown `CheckError` in
`StateT AState (Except …)` carries nothing — so the error arm claims nothing
about the memo, exactly as it claims nothing about the state. -/
def EOut {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (rm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)
    (x : Except Arena.CheckError ((Std.HashMap ConLeche.Expr EIdx × β) × AState)) :
    Prop :=
  match o with
  | .Ok r => ∃ m' lst', x = .ok ((m', A r), lst') ∧ EMemoRel rm m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- `EOut` at the Rust's outcome TRIPLE. -/
def SimEM {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)
    (x : AM (Std.HashMap ConLeche.Expr EIdx × β)) : Prop :=
  EOut A pers lst o.1 o.2.1 o.2.2 (x.run lst)

/-! ## `arena::checker_base`'s `Bool` memo, threaded two ways

`consts_resolve_f_go` and `all_level_params_defined_go` thread a
`HashMap2<EIdx, bool>` exactly as `expr_ops`' three memoised walks do, so the
relation is `Refine2/ExprOps/Read.lean`'s **`LMemoRel`**, reused rather than
re-declared.  What is new is that the Rust returns the memo OUTSIDE the
`Result` (a moved value comes back whatever happened) where the twin returns
it INSIDE, beside the answer — and that the second of the two does not thread
the state at all.  Two shapes, three lines each. -/

/-- A `Bool`-memo walk that threads the state: `(Result α) × AState × memo`
against the twin's `AM (β × Std.HashMap EIdx Bool)`. -/
def SimBM {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (x : AM (β × Std.HashMap EIdx Bool)) : Prop :=
  match o.1 with
  | .Ok r => ∃ m' lst', x.run lst = .ok ((A r, m'), lst') ∧ ExprOps.LMemoRel o.2.2 m' ∧
      AStateRel pers o.2.1 lst' ∧ AStateInv pers o.2.1 ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e (x.run lst)

/-- A `Bool`-memo walk that only READS the state: `(Result α) × memo`.
`all_level_params_defined_go` is the one, and it is a reader because the
level-parameter test interns nothing. -/
def SimBR {α β : Type} (A : α → β) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (x : AM (β × Std.HashMap EIdx Bool)) : Prop :=
  match o.1 with
  | .Ok r => ∃ m', x.run lst = .ok ((A r, m'), lst) ∧ ExprOps.LMemoRel o.2 m'
  | .Err e => AErrSim e (x.run lst)

/-! ## The containers these two tiers abstract

Every one is a `Vec` against the container `Arena/Promote.lean`,
`Arena/Intern.lean` and `Arena/Checker.lean` chose, and every choice is
con-leche's own.  The `…From` family is DESIGN §3.4's standing
`List`-as-cursor deviation: where the twin recurses structurally on a `List`,
the Rust takes the whole `Vec` and an index. -/

def absNIdxL (v : alloc.vec.Vec arena.handle.NIdx) : List NIdx := v.val.map absNIdx
def absEIdxL (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx := v.val.map absEIdx
def absLIdxL (v : alloc.vec.Vec arena.handle.LIdx) : List LIdx := v.val.map absLIdx

def absNIdxLFrom (v : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) : List NIdx :=
  (v.val.drop i.val).map absNIdx
def absEIdxLFrom (v : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) : List EIdx :=
  (v.val.drop i.val).map absEIdx
def absLIdxLFrom (v : alloc.vec.Vec arena.handle.LIdx) (i : Std.Usize) : List LIdx :=
  (v.val.drop i.val).map absLIdx

def absIRecRuleL (v : alloc.vec.Vec arena.env.IRecRule) : List IRecRule :=
  v.val.map absIRecRule
def absIRecRuleLFrom (v : alloc.vec.Vec arena.env.IRecRule) (i : Std.Usize) :
    List IRecRule := (v.val.drop i.val).map absIRecRule

def absICIL (v : alloc.vec.Vec arena.env.IConstantInfo) : List IConstantInfo :=
  v.val.map absIConstantInfo
def absICILFrom (v : alloc.vec.Vec arena.env.IConstantInfo) (i : Std.Usize) :
    List IConstantInfo := (v.val.drop i.val).map absIConstantInfo

def absIDeclL (v : alloc.vec.Vec arena.env.IDeclaration) : List IDeclaration :=
  v.val.map absIDeclaration
def absIDeclLFrom (v : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize) :
    List IDeclaration := (v.val.drop i.val).map absIDeclaration

/-- `Vec<(Vec<EIdx>, EIdx)>` as the twin's `List (List EIdx × EIdx)` —
`divModCertStmts`' open characterization statements: per certificate, the list
of hypothesis types and the characteristic equation. -/
def absStmts (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    List (List EIdx × EIdx) :=
  v.val.map fun p => (p.1.val.map absEIdx, absEIdx p.2)

/-- The same from a cursor on. -/
def absStmtsFrom
    (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) : List (List EIdx × EIdx) :=
  (v.val.drop i.val).map fun p => (p.1.val.map absEIdx, absEIdx p.2)

/-- `Vec<(EIdx, EIdx)>` as the twin's `List (EIdx × EIdx)` — `certifyNatEqs`'
equation list. -/
def absEqPairs (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) :
    List (EIdx × EIdx) := v.val.map fun p => (absEIdx p.1, absEIdx p.2)

def absEqPairsFrom (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) : List (EIdx × EIdx) :=
  (v.val.drop i.val).map fun p => (absEIdx p.1, absEIdx p.2)

/-- `Vec<(EIdx, BinderMeta)>` as the twin's `Array (EIdx × BinderMeta)` —
`domsMatchAux`'s subject.  con-leche's `List` version is quadratic on a wide
telescope and its `Array` twin is what the checker runs, so the twin is the
array one. -/
def absBinderArr (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    Array (EIdx × ConLeche.BinderMeta) :=
  (v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray

def absExprLFrom (v : alloc.vec.Vec kernel.expr.Expr) (i : Std.Usize) :
    List ConLeche.Expr := (v.val.drop i.val).map ConRon.Refine.absExpr
def absCIListFrom (v : alloc.vec.Vec kernel.env.ConstantInfo) (i : Std.Usize) :
    List ConLeche.ConstantInfo := (v.val.drop i.val).map ConRon.Refine.absConstantInfo
def absRecRuleLFrom (v : alloc.vec.Vec kernel.env.RecRule) (i : Std.Usize) :
    List ConLeche.RecRule := (v.val.drop i.val).map ConRon.Refine.absRecRule
def absDeclLFrom (v : alloc.vec.Vec kernel.env.Declaration) (i : Std.Usize) :
    List ConLeche.Declaration := (v.val.drop i.val).map ConRon.Refine.absDeclaration
def absLevelLFrom (v : alloc.vec.Vec kernel.level.Level) (i : Std.Usize) :
    List ConLeche.Level := (v.val.drop i.val).map ConRon.Refine.absLevel
def absNameLFrom (v : alloc.vec.Vec kernel.name.Name) (i : Std.Usize) :
    List ConLeche.Name := (v.val.drop i.val).map ConRon.Refine.absName
def absBasisKindLFrom (v : alloc.vec.Vec kernel.env.BasisKind) (i : Std.Usize) :
    List ConLeche.BasisKind := (v.val.drop i.val).map ConRon.Refine.absBasisKind

attribute [simp] absNIdxL absEIdxL absLIdxL absNIdxLFrom absEIdxLFrom absLIdxLFrom
  absIRecRuleL absIRecRuleLFrom absICIL absICILFrom absIDeclL absIDeclLFrom
  absStmts absStmtsFrom absEqPairs absEqPairsFrom absBinderArr absExprLFrom absCIListFrom absRecRuleLFrom absDeclLFrom absLevelLFrom
  absNameLFrom absBasisKindLFrom

/-! ## The environment index's own invariant

`Refine2/AbsState.lean`'s `IFEnvRel` reads the Rust index through
`HashMap2.toFun`, which is a specification of a well-formed table and says
nothing about a malformed one.  Every other `RelOn` of this tower is paired
with an `Inv` in `AStateInv`; the environment is not in the state, so its
`Inv` travels with it.

**Second clause, task #97-P5-Checker-2**: the visibility counter never runs
past the constant list.  It is what discharges task #97-P5-Checker's **finding
C** — `promote_new` DECLINES when `k > fe.env.consts.len()` where the twin
promotes, and `check_decl_step`'s `k` is `fe'.visibleBelow - fe.visibleBelow`,
so `k ≤ fe'.visibleBelow ≤ |fe'.consts|` is exactly the hypothesis the call
site needs.  That finding predicted the clause would be *"Theorem 1's to
carry"*; it is cheaper than that, because the port's own `IFEnv` maintains it:
`mk_ifenv` sets the counter to the list's length and `ifenv_push` grows both
by one.  It belongs here, beside the index's `Inv`, for the same reason the
index's does. -/
def IFEnvInv (rf : arena.env.IFEnv) : Prop :=
  Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rf.idx ∧
    rf.visible_below.val ≤ rf.env.consts.val.length ∧
    ∀ n p, ConRon.Refine.HashMap2.toFun rf.idx n = some p →
      p.2.val < rf.env.consts.val.length

theorem IFEnvInv.idxInv {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rf.idx := h.1

/-- The counter is a bound on the constant list — finding C, at the call
site. -/
theorem IFEnvInv.visBound {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    rf.visible_below.val ≤ rf.env.consts.val.length := h.2.1

/-- **Every position the index stores fits a `usize`** — task #97-P5-Core-2's
`CoreCtx.idxPos`, which `ifenv_find_abs` is the only consumer of.

It is an INVARIANT and not a platform assumption, and the write sites are why:
every position ever stored is a `Vec` index or a `Vec` length cast up from
`usize` — `arena::env::mk_ifenv_go` stores `i as u64` for the cursor `i`,
`ifenv_push` and `ifenv_push_temp` store `fe.env.consts.len() as u64`,
`arena::promote::index_promoted` stores `(j - 1) as u64` for its `usize`
cursor, and `ifenv_pop_temp` puts back a row it took OUT of the index.  There
is no other writer.  So the `pos as usize` in `ifenv_find` — which Aeneas
models as a truncating cast — is the identity at every reachable row, and
the Rust needs no test it does not already have. -/
theorem IFEnvInv.idxPos {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    ∀ n p, ConRon.Refine.HashMap2.toFun rf.idx n = some p → p.2.val ≤ Std.Usize.max :=
  fun n p hp => le_of_lt (lt_of_lt_of_le (h.2.2 n p hp) rf.env.consts.property)

/-- **Every position the index stores is IN RANGE of the constant list** —
task #97-P5-Checker round 3's strengthening of the clause above, and the one
`ifenv_push` needs.

The weaker clause (*"the position fits a `usize`"*) is not enough to push:
`IFEnvRel.idx` reads the port's index through `consts[p.2]?`, and an
OUT-OF-RANGE stored position answers `none`, which the relation matches
against a twin index that has no entry there.  Append one constant and that
same row is suddenly in range and answers `some ci` — against a twin index
that still has nothing.  So `IFEnvRel rf' (lf.push …)` is **false** unless
the index is known to store no position at or past the end, and
`ifenv_push_refines` below cannot be proved from the weaker clause.

It is an invariant of the port for exactly the reason the weaker one was:
`mk_ifenv_go` stores its `Vec` cursor `i < len`, `ifenv_push` and
`ifenv_push_temp` store the length BEFORE the `push` that makes it an index,
`arena::promote::index_promoted` stores `(j - 1)` for a cursor `j ≥ 1`, and
`ifenv_pop_temp` puts back a row it took out.  There is no other writer, and
no Rust test is missing. -/
theorem IFEnvInv.idxRange {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    ∀ n p, ConRon.Refine.HashMap2.toFun rf.idx n = some p →
      p.2.val < rf.env.consts.val.length :=
  h.2.2

/-! ## The environment relation a FOLD has to carry (task #97-P5-Checker-2)

`IFEnvRel` alone does not compose.  Every statement of this tier takes
`hfe : IFEnvRel rf lf` **and** `hfinv : IFEnvInv rf` — the second because
`IFEnvRel.idx` reads the port's index through `HashMap2.toFun`, which
specifies a well-formed table and says nothing about a malformed one — and
every one of them CONCLUDES `IFEnvRel` alone.  A fold then cannot take its own
step twice: `check_decls_pure_go` feeds `check_decl_step`'s answer back into
itself and has no `IFEnvInv` for it, and `install_then_check` hands
`annot_fold`'s environment to `check_pending_list`, which demands one.

So the RESULT relation of every `IFEnv`-returning statement on the fold's path
is this pair.  It is not a new obligation in substance — the port builds the
index with `HashMap2::insert`, which preserves `Inv` — but it has to be SAID,
and task #97-P5-Checker's statements did not say it.  The two capstones keep
their public conclusion at `IFEnvRel` alone (DESIGN §8.2's own sentence) and
weaken this at the last step. -/

/-- **The environment, related and well formed** — the result relation a fold
step has to carry. -/
def IFEnvRelI (rf : arena.env.IFEnv) (lf : IFEnv) : Prop :=
  IFEnvRel rf lf ∧ IFEnvInv rf

theorem IFEnvRelI.mk {rf : arena.env.IFEnv} {lf : IFEnv} (h : IFEnvRel rf lf)
    (hi : IFEnvInv rf) : IFEnvRelI rf lf := ⟨h, hi⟩

theorem IFEnvRelI.rel {rf : arena.env.IFEnv} {lf : IFEnv} (h : IFEnvRelI rf lf) :
    IFEnvRel rf lf := h.1

theorem IFEnvRelI.inv {rf : arena.env.IFEnv} {lf : IFEnv} (h : IFEnvRelI rf lf) :
    IFEnvInv rf := h.2

/-! ## `arena::env::ifenv_push` — the one environment write every install route
folds over (task #97-P5-Checker round 3)

`ifenv_push` is the port's `IFEnv.push`: the index row is written at the
constant list's CURRENT length and the list grows by one, where the twin
conses onto a newest-first list and inserts the constant itself.  Every
`cons_*` fold of the install routes — `arena::inductives`' `cons_sum_ctors`
and `cons_sum_ctors_f` above all — is this step iterated, so this is the step
that has to be stated once rather than fifty times.

It lives here because both halves are this file's: `IFEnvRel` composes the
index probe with the array read (`Refine2/AbsState.lean`), and `IFEnvInv` is
what makes that composition survive an append (`IFEnvInv.idxRange`). -/

/-- `arena::env::i_constant_info_name` is the twin's `IConstantInfo.name`.

**Moved down from `Refine2/Inductives/Shape.lean` by task #97-P5-Checker
round 4**, where it was public and this file had a private copy (this file is
below that one, so neither could see the other).  One lemma now, here, where
both tiers reach it. -/
theorem i_constant_info_name_abs {c : arena.env.IConstantInfo}
    {o : arena.handle.NIdx} (h : arena.env.i_constant_info_name c = ok o) :
    absNIdx o = (absIConstantInfo c).name := by
  rw [arena.env.i_constant_info_name.eq_def] at h
  cases c <;> simp only [absIConstantInfo, IConstantInfo.name, absIConstantVal,
    absIProjTable, dupId_nidx _ _ h]

/-- **A handle comparison IS the abstraction's.**  `eq2` on an `NIdx` is word
equality and `absNIdx` is injective, so the port's test and the twin's `==`
agree at both signs.  Moved down from `Refine2/Inductives/Shape.lean` (task
#97-P5-Checker round 4); `Refine2/Checker/Canon.lean` had a private copy in
`decide` form, which `nidx_eq2_abs_decide` now is. -/
theorem nidx_eq2_abs {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

/-- The same at an `EIdx`. -/
theorem eidx_eq2_abs {a b : arena.handle.EIdx} {o : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absEIdx a == absEIdx b) := by
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absEIdx a ≠ absEIdx b := fun hc => hab (absEIdx_inj hc)
    simp [h1, h2]

/-- `nidx_eq2_abs` in `decide` form — the spelling `Refine2/Checker/Canon.lean`'s
record comparisons consume. -/
theorem nidx_eq2_abs_decide {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = decide (absNIdx a = absNIdx b) := by
  rw [nidx_eq2_abs h]; exact beq_eq_decide _ _

/-- `eidx_eq2_abs` in `decide` form. -/
theorem eidx_eq2_abs_decide {a b : arena.handle.EIdx} {o : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = decide (absEIdx a = absEIdx b) := by
  rw [eidx_eq2_abs h]; exact beq_eq_decide _ _

/-- **`ifenv_push` ⊑ `IFEnv.push`, relation and invariant together.**

The three clauses, in order:

* `env` — the port appends and `absIEnv` reverses, so the appended constant is
  the twin's HEAD;
* `idx` — at the pushed name the port's row is `(visible_below, |consts|)` and
  `consts[|consts|]?` of the GROWN list is the pushed constant, which is the
  twin's `(visibleBelow, ci)`; at every other name `IFEnvInv.idxRange` says the
  stored position was already in range, so the append does not change what it
  reads;
* `visibleBelow` — both counters advance by one.

and the invariant: the index's `Inv` is `HashMap2::insert`'s, the counter
bound is the old one plus one on both sides, and the new row's position is
`|consts|`, which is in range of `|consts| + 1`. -/
theorem ifenv_push_refines {rf rf' : arena.env.IFEnv} {lf : IFEnv}
    {ci : arena.env.IConstantInfo}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (h : arena.env.ifenv_push rf ci = ok rf') :
    IFEnvRel rf' (lf.push (absIConstantInfo ci)) ∧ IFEnvInv rf' := by
  rw [arena.env.ifenv_push] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  -- the cast on the length is the identity
  have hsv : s.val = rf.env.consts.val.length := by
    simp only [lift, Result.ok.injEq] at hs
    subst hs
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  -- the index row written, and the table's `Inv` re-established
  obtain ⟨hinv', -, hupd, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
      hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hvv : v.val = rf.env.consts.val ++ [ci] := ConRon.Refine.vec_push_val hv
  have hc1v : c1.val = rf.visible_below.val + 1 := by
    simpa using ConRon.Refine.Nat.uadd_val hc1
  have hrf' : rf' = { env := { consts := v }, idx := q.2, visible_below := c1 } :=
    (Result.ok_injective h).symm
  subst hrf'
  have hname : absNIdx n = (absIConstantInfo ci).name := i_constant_info_name_abs hn
  refine ⟨⟨?_, ?_, ?_⟩, hinv', ?_, ?_⟩
  · -- the constant list
    show (lf.push (absIConstantInfo ci)).env = absIEnv _
    simp only [IFEnv.push, absIEnv, hvv, List.map_append, List.reverse_append]
    rw [hfe.env]
    simp [absIEnv]
  · -- the index
    intro m
    rw [hupd]
    simp only [IFEnv.push, _root_.Std.HashMap.getElem?_insert, Function.update_apply]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl, if_pos (by simp [hname])]
      simp only [Option.bind, hvv]
      rw [List.getElem?_append_right (by omega), hsv, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.map_some]
      rw [hfe.visibleBelow]
    · rw [if_neg hm]
      have hne : ¬ ((absIConstantInfo ci).name == absNIdx m) = true := by
        simp only [beq_iff_eq]
        intro hc
        exact hm (absNIdx_inj (hc.symm.trans hname.symm))
      rw [if_neg hne, ← hfe.idx m]
      cases hp : ConRon.Refine.HashMap2.toFun rf.idx m with
      | none => simp
      | some p =>
        simp only [Option.bind, hvv]
        rw [List.getElem?_append_left (hfinv.idxRange m p hp)]
  · -- the counter
    show (lf.push (absIConstantInfo ci)).visibleBelow = absU c1
    simp only [IFEnv.push]
    rw [hfe.visibleBelow]
    simp [absU, hc1v]
  · -- the counter is still a bound
    rw [hvv, hc1v]
    have := hfinv.visBound
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · -- every stored position is still in range
    intro m p hp
    rw [hupd, Function.update_apply] at hp
    rw [hvv]
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl] at hp
      obtain rfl : p = (rf.visible_below, s) := (Option.some_injective _ hp).symm
      simp only [hsv]
      omega
    · rw [if_neg hm] at hp
      have := hfinv.idxRange m p hp
      omega

/-! ## The telescope opens' LENGTH (task #97-P5-Checker round 3)

`Arena/CheckerBase.lean`'s `openPisAtFvarsF n cty i` opens the first `n`
`∀`-binders at fresh free variables and hands back the list it made.  **That
list has exactly `n` entries**, and the fact is not decoration:
`Arena/Inductives/NativeInstall.lean`'s `nativeOpenedOk` dispatches its
per-field walk on TWO scrutinees,

    match xFvs[i]?, ks.getD i .ordinary with … | _, _ => pure false

over `i ∈ List.range nF`, where `Refine2/Inductives/Spec.lean`'s transcription
dispatches on the kind alone and reads the variable totally.  The two agree
exactly when `xFvs.length = nF`, so `nativeOpenedOk_unfold` — the Inductives
tier's owed equation — cannot be repaired without this.

It lives here because `openPisAtFvarsF` is `arena::checker_base`'s twin and
this is the shared base both tiers import; `Arena/**` carries definitions and
no theorems (DESIGN §8.4), so a fact ABOUT a twin belongs on this side of the
line.

`am_run_bind_ok` is the peel these three inductions run on — the `ok` half of
`Core/Induction.lean`'s `am_run_bind`, which is a sibling of this file rather
than below it, hence the second spelling. -/

theorem am_run_bind' {α β : Type} (m : AM α) (k : α → AM β) (lst : AState) :
    ((m >>= k)).run lst = (m.run lst) >>= fun p => (k p.1).run p.2 := rfl

theorem am_run_bind_ok {α β : Type} {m : AM α} {k : α → AM β} {ls ls' : AState}
    {b : β} (h : (m >>= k).run ls = .ok (b, ls')) :
    ∃ a ls₁, m.run ls = .ok (a, ls₁) ∧ (k a).run ls₁ = .ok (b, ls') := by
  rw [am_run_bind'] at h
  revert h
  cases m.run ls with
  | error e => intro h; exact absurd h (by simp [Bind.bind, Except.bind])
  | ok p =>
    obtain ⟨a, s⟩ := p
    intro h
    exact ⟨a, s, rfl, h⟩

private theorem pure_none_ne {ls ls' : AState} {fvs : List EIdx} {r : EIdx}
    (h : (pure none : AM (Option (List EIdx × EIdx))).run ls
      = .ok (some (fvs, r), ls')) : False := by
  replace h : (Except.ok ((none : Option (List EIdx × EIdx)), ls)
      : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
      = Except.ok (some (fvs, r), ls') := h
  simp at h

theorem openPisAtFvars_length {n : Nat} {e : EIdx} {i : Nat} {ls ls' : AState}
    {fvs : List EIdx} {r : EIdx}
    (h : (openPisAtFvars n e i).run ls = .ok (some (fvs, r), ls')) :
    fvs.length = n := by
  induction n generalizing e i ls ls' fvs r with
  | zero =>
    rw [openPisAtFvars] at h
    replace h : (Except.ok (((some ([], e)) : Option (List EIdx × EIdx)), ls)
        : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
        = Except.ok (some (fvs, r), ls') := h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1.1]
    rfl
  | succ n ih =>
    rw [openPisAtFvars] at h
    obtain ⟨v, ls1, -, h⟩ := am_run_bind_ok h
    cases v
    case forallE dom body mm =>
      obtain ⟨fv, ls2, -, h⟩ := am_run_bind_ok h
      obtain ⟨b, ls3, -, h⟩ := am_run_bind_ok h
      obtain ⟨o, ls4, ho, h⟩ := am_run_bind_ok h
      cases o with
      | none => exact (pure_none_ne h).elim
      | some p =>
        obtain ⟨fvs₀, r₀⟩ := p
        replace h : (Except.ok (((some (fv :: fvs₀, r₀)) : Option (List EIdx × EIdx)), ls4)
            : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
            = Except.ok (some (fvs, r), ls') := h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.1.1]
        simp [ih ho]
    all_goals exact (pure_none_ne h).elim

theorem openPisAtFvarsFGo_length : ∀ {acc : Array EIdx} {n : Nat} {e : EIdx}
    {i : Nat} {ls ls' : AState} {fvs : List EIdx} {r : EIdx},
    (openPisAtFvarsFGo acc n e i).run ls = .ok (some (fvs, r), ls') →
    fvs.length = n := by
  intro acc n
  induction n generalizing acc with
  | zero =>
    intro e i ls ls' fvs r h
    rw [openPisAtFvarsFGo] at h
    obtain ⟨x, ls1, -, h⟩ := am_run_bind_ok h
    replace h : (Except.ok (((some ([], x)) : Option (List EIdx × EIdx)), ls1)
        : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
        = Except.ok (some (fvs, r), ls') := h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1.1]
    rfl
  | succ n ih =>
    intro e i ls ls' fvs r h
    rw [openPisAtFvarsFGo] at h
    obtain ⟨v, ls1, -, h⟩ := am_run_bind_ok h
    cases v
    case forallE dom body mm =>
      obtain ⟨d, ls2, -, h⟩ := am_run_bind_ok h
      obtain ⟨fv, ls3, -, h⟩ := am_run_bind_ok h
      obtain ⟨o, ls4, ho, h⟩ := am_run_bind_ok h
      cases o with
      | none => exact (pure_none_ne h).elim
      | some p =>
        obtain ⟨fvs₀, r₀⟩ := p
        replace h : (Except.ok (((some (fv :: fvs₀, r₀)) : Option (List EIdx × EIdx)), ls4)
            : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
            = Except.ok (some (fvs, r), ls') := h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.1.1]
        simp [ih ho]
    all_goals exact (pure_none_ne h).elim

theorem openPisAtFvarsF_length {n : Nat} {e : EIdx} {i : Nat} {ls ls' : AState}
    {fvs : List EIdx} {r : EIdx}
    (h : (openPisAtFvarsF n e i).run ls = .ok (some (fvs, r), ls')) :
    fvs.length = n := by
  rw [openPisAtFvarsF] at h
  obtain ⟨o, ls1, ho, h⟩ := am_run_bind_ok h
  cases o with
  | none => exact openPisAtFvars_length h
  | some p =>
    obtain ⟨fvs₀, r₀⟩ := p
    replace h : (Except.ok (((some (fvs₀, r₀)) : Option (List EIdx × EIdx)), ls1)
        : Except Arena.CheckError (Option (List EIdx × EIdx) × AState))
        = Except.ok (some (fvs, r), ls') := h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1.1]
    exact openPisAtFvarsFGo_length ho

/-! ## The declaration boundary, as a fact about the TWIN
(task #97-P5-Checker round 3)

`Refine2/Core/Bracket.lean`'s `BrOK` is the boundary a bracketed step is
entered at — the twin store well formed and its scratch tier closed — and the
three bracketed statements of `Refine2/Checker/Top.lean` (`check_pending`,
`check_decl_step`, `annot_step`) each need one.  Since task #97-P5-Specs put
`StoreWF ls.store` into `AStateRel` (finding 16) the well-formedness half is
free at every state the relation holds of; the FLAG half is not, and must not
be — it is false of the state INSIDE the bracket, which is exactly a state
`AStateRel` holds of.

**So the flag threads, and the cheapest way to thread it is not to touch a
refinement statement at all.**  `dropScratch` closes the tier whatever ran
before it, so *"this twin action leaves the tier closed"* is a fact about the
TWIN alone, quantified over the state — `Refine2/Core/Bracket.lean`'s `TwinWF`
shape, and it threads through a fold for the same reason.  A bracketed step
then carries one extra HYPOTHESIS (`BrOK lst`) and no extra conclusion: the
fold rebuilds the next boundary from `AStateRel.storeWF` and the `_off` lemma
of whatever it just ran. -/

/-- The twin's `dropScratch`, run. -/
theorem dropScratch_run (ls : AState) :
    (dropScratch : AM Unit).run ls
      = .ok ((), { ls with store := ls.store.dropScratch, caches := Caches.empty })
  := rfl

/-- **`dropScratch` closes the tier**, whatever ran before it. -/
theorem dropScratch_off {ls ls' : AState} {v : Unit}
    (h : (dropScratch : AM Unit).run ls = .ok (v, ls')) :
    ls'.store.scratchOn = false := by
  rw [dropScratch_run] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  rfl

/-- `dropScratch` followed by anything that leaves the STATE alone — the tail
of every bracketed twin, which is `dropScratch; pure <something>`. -/
theorem dropScratch_bind_off {α : Type} {k : Unit → AM α} {ls ls' : AState}
    {v : α}
    (hk : ∀ (u : Unit) (s s' : AState) (w : α), (k u).run s = .ok (w, s') →
      s' = s)
    (h : ((dropScratch : AM Unit) >>= k).run ls = .ok (v, ls')) :
    ls'.store.scratchOn = false := by
  obtain ⟨u, ls₁, h1, h2⟩ := am_run_bind_ok h
  rw [hk u ls₁ ls' v h2]
  exact dropScratch_off h1

/-- A `pure`'s VALUE, off a run. -/
theorem am_run_pure_val {α : Type} {a : α} {s s' : AState} {w : α}
    (h : (pure a : AM α).run s = .ok (w, s')) : w = a := by
  replace h : (Except.ok (a, s) : Except Arena.CheckError (α × AState))
      = Except.ok (w, s') := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1.symm

/-- The side condition of `dropScratch_bind_off` at a `pure`. -/
theorem am_run_pure_state {α : Type} {a : α} {s s' : AState} {w : α}
    (h : (pure a : AM α).run s = .ok (w, s')) : s' = s := by
  replace h : (Except.ok (a, s) : Except Arena.CheckError (α × AState))
      = Except.ok (w, s') := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-! ## The promote window, closed (task #97-P5-Checker round 4)

**The bridge between `AStateRelW` and `AStateRel` is `dropScratch`, and it is
one lemma: `bracket_close_w`.**  A bracketed step runs its body at the strong
relation, enters the promotion at the weak one (`AStateRelW.of_rel`, free),
and leaves the promotion at the weak one — `internPersistent` breaks `fresh`
(task #97-P5-Fresh) — so what the bracket's closing half is handed is
`AStateRelW`, where `Refine2/Core/Bracket.lean`'s `bracket_close` asks for
`AStateRel`.  `bracket_close` needs the strong relation for exactly two
things, and neither of them reads `fresh`:

* `drop_scratch_refines`' post-state `storeWF` — which the WEAK invariant
  gives as well, through `StoreWF'.dropScratch_wf` (task #97-P5-Fresh §4:
  `wf_of_scr_empty` never read the input's `fresh`);
* `ext_bracket`'s `StoreWF b` — the tier discipline that makes a PERSISTENT
  handle's denotation survive the drop.  Its proof reads `childOK`'s
  persistence conjunct, the four ranks and `bmChildOK`, all of which the weak
  invariant keeps; the four `denote*Aux_dropScratch` inductions below are the
  strong ones with `WFAt` replaced by `WFAt'` and not a step changed.

So the relation is weak exactly across the promote window and strong on both
sides of it, and **no statement above the bracket weakens**.  The four
inductions belong beside their strong siblings in `Arena/WFProofs.lean`;
they are here because that file is not this tier's lane. -/

theorem _root_.ConRon.Arena.NWFAt'.rank_lt {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk)
    {i : NIdx} (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := NStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem _root_.ConRon.Arena.LWFAt'.rank_lt {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk)
    {i : LIdx} (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := LStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem _root_.ConRon.Arena.EWFAt'.rank_lt {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk)
    {i : EIdx} (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := EStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem _root_.ConRon.Arena.EWFAt'.bmPers {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) (i : EIdx)
    (hp : i.isPersistent = true) :
    ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true :=
  fun ty b mi hh => (h.bmChildOK i ty b mi hh).2.1 hp

theorem denoteNAux_dropScratch' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    ∀ (f : Nat) (i : NIdx) (x : ConLeche.Name), i.isPersistent = true →
      denoteNAux st f i = some x → denoteNAux st.dropScratch f i = some x := by
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteNAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteNAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [NStore.view_dropScratch_pers st hp]; exact hv, ?_⟩
    cases v with
    | anonymous => exact hd
    | str p s =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q ((h.childOK i _ hv p (by simp [NNodeView.children])).2.2 hp) hq, he⟩
    | num p n =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q ((h.childOK i _ hv p (by simp [NNodeView.children])).2.2 hp) hq, he⟩

theorem denoteN_dropScratch_pers' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk)
    {i : NIdx} {x : ConLeche.Name} (hp : i.isPersistent = true)
    (hd : denoteN st i = some x) : denoteN st.dropScratch i = some x := by
  have h' := NStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteN_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [NStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteNAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteNAux_dropScratch' h _ i x hp hd
  rw [denoteN, denoteNAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

theorem denoteLAux_dropScratch' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    ∀ (f : Nat) (i : LIdx) (x : ConLeche.Level), i.isPersistent = true →
      denoteLAux st f i = some x → denoteLAux st.dropScratch f i = some x := by
  obtain ⟨rkn, hn⟩ := h.ns
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteLAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteLAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [LStore.view_dropScratch_pers st hp]; exact hv, ?_⟩
    cases v with
    | zero => exact hd
    | succ u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih u q ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) hq, he⟩
    | max u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) ha,
        ih w b ((h.childOK i _ hv w (by simp [LNodeView.lchildren])).2.2 hp) hb, he⟩
    | imax u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) ha,
        ih w b ((h.childOK i _ hv w (by simp [LNodeView.lchildren])).2.2 hp) hb, he⟩
    | param n =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      refine ⟨q, ?_, he⟩
      exact denoteN_dropScratch_pers' hn
        ((h.nchildOK i _ hv n (by simp [LNodeView.nchildren])).2 hp) hq

theorem denoteL_dropScratch_pers' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk)
    {i : LIdx} {x : ConLeche.Level} (hp : i.isPersistent = true)
    (hd : denoteL st i = some x) : denoteL st.dropScratch i = some x := by
  have h' := LStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteL_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [LStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteLAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteLAux_dropScratch' h _ i x hp hd
  rw [denoteL, denoteLAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

theorem denoteLList_dropScratch' {ls : LStore} {rk : LIdx → Nat} (h : LWFAt' ls rk) :
    ∀ (us : List LIdx) (xs : List ConLeche.Level), (∀ c ∈ us, c.isPersistent = true) →
      denoteLList ls us = some xs → denoteLList ls.dropScratch us = some xs := by
  intro us
  induction us with
  | nil => intro xs _ hd; exact hd
  | cons u rest ih =>
    intro xs hp hd
    simp only [denoteLList, opt2_eq_some_iff] at hd ⊢
    obtain ⟨a, b, ha, hb, he⟩ := hd
    exact ⟨a, b, denoteL_dropScratch_pers' h (hp u (by simp)) ha,
      ih b (fun c hc => hp c (by simp [hc])) hb, he⟩

theorem denoteLs_dropScratch_pers' {st : LsStore} (h : LsWF' st) {i : LsIdx}
    {xs : List ConLeche.Level} (hp : i.isPersistent = true) (hd : denoteLs st i = some xs) :
    denoteLs st.dropScratch i = some xs := by
  obtain ⟨rkl, hl⟩ := h.ls
  obtain ⟨us, hus, hlist⟩ := denoteLs_view hd
  rw [denoteLs, LsStore.view_dropScratch_pers st hp, hus]
  exact denoteLList_dropScratch' hl us xs
    (fun c hc => (h.lchildOK i us hus c hc).2 hp) hlist

theorem denoteEAux_dropScratch' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    ∀ (f : Nat) (i : EIdx) (x : ConLeche.Expr), i.isPersistent = true →
      denoteEAux st f i = some x → denoteEAux st.dropScratch f i = some x := by
  have hlsw : LsWF' st.lss := h.lss
  obtain ⟨rkl, hl⟩ : LStoreWF' st.ls := hlsw.ls
  obtain ⟨rkn, hn⟩ : NStoreWF' st.ns := hl.ns
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteEAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteEAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [EStore.view_dropScratch_pers st (h.bmPers i hp) hp]; exact hv, ?_⟩
    cases v with
    | bvar _ => exact hd
    | lit _ => exact hd
    | fvar j ty =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih ty q ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hq, he⟩
    | sort u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      refine ⟨q, ?_, he⟩
      exact denoteL_dropScratch_pers' hl
        ((h.lchildOK i _ hv u (by simp [ENodeView.lchildren])).2 hp) hq
    | const n us =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      refine ⟨a, b, ?_, ?_, he⟩
      · exact denoteN_dropScratch_pers' hn
          ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) ha
      · exact denoteLs_dropScratch_pers' hlsw
          ((h.lschildOK i _ hv us (by simp [ENodeView.lschildren])).2 hp) hb
    | app g a =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih g p ((h.childOK i _ hv g (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih a q ((h.childOK i _ hv a (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | lam ty b m =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih b q ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | forallE ty b m =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih b q ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | letE ty val b =>
      simp only [opt3_eq_some_iff] at hd ⊢
      obtain ⟨p, q, r, hp1, hq1, hr1, he⟩ := hd
      exact ⟨p, q, r,
        ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih val q ((h.childOK i _ hv val (by simp [ENodeView.echildren])).2.2 hp) hq1,
        ih b r ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hr1, he⟩
    | proj n j e =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      refine ⟨p, q, ?_, ih e q ((h.childOK i _ hv e (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
      exact denoteN_dropScratch_pers' hn
        ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) hp1

theorem EStore.dropScratch_denote_pers' {st : EStore} (h : StoreWF' st)
    {i : EIdx} {e : ConLeche.Expr} (hp : i.isPersistent = true)
    (hd : denoteE st i = some e) : denoteE st.dropScratch i = some e := by
  obtain ⟨rk, h⟩ := h
  have h' := EStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteE_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [EStore.view_dropScratch_pers st (h.bmPers i hp) hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteEAux st.dropScratch (st.nodeCount + 1) i = some e :=
    denoteEAux_dropScratch' h _ i e hp hd
  rw [denoteE, denoteEAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

/-- `Refine2/Core/Bracket.lean`'s `ext_dropScratch` at the WEAK invariant. -/
theorem ext_dropScratch' {a b : EStore} (hc : ScratchClosed a) (hwf : StoreWF' b)
    (h : Ext a b) : Ext a b.dropScratch := by
  obtain ⟨rk, hwa⟩ := hwf
  have hwfE : StoreWF' b := ⟨rk, hwa⟩
  have hlss : LsWF' b.lss := hwa.lss
  obtain ⟨rkl, hls⟩ : LStoreWF' b.lss.ls := hlss.ls
  obtain ⟨rkn, hns⟩ : NStoreWF' b.lss.ls.ns := hls.ns
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i n hd
    exact denoteN_dropScratch_pers' hns (hc.lss.ls.ns.pers hd) (h.lss.ls.ns i n hd)
  · intro i u hd
    exact denoteL_dropScratch_pers' hls (hc.lss.ls.pers hd) (h.lss.ls.lvl i u hd)
  · intro i us hd
    exact denoteLs_dropScratch_pers' hlss (hc.lss.pers hd) (h.lss.lst i us hd)
  · intro i e hd
    exact EStore.dropScratch_denote_pers' hwfE (hc.pers hd) (h.expr i e hd)

/-- `ext_bracket` at the WEAK invariant: **the bracket, as an `Ext`, across a
promotion**. -/
theorem ext_bracket' {a b : EStore} (hc : ScratchClosed a) (hwf : StoreWF' b)
    (h : Ext a.enableScratch b) : Ext a b.dropScratch :=
  ext_dropScratch' hc hwf (Ext.trans hc.ext h)

/-- `drop_scratch_refines` from the promote window's relation: the WEAK
relation in, the STRONG one out — `dropScratch` is where `fresh` comes back. -/
theorem drop_scratch_refines_w {pers st lst st'}
    (hrel : AStateRelW pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.drop_scratch st = ok st') :
    (dropScratch : AM Unit).run lst = .ok ((),
        { lst with store := lst.store.dropScratch, caches := Caches.empty }) ∧
      AStateRel pers st'
        { lst with store := lst.store.dropScratch, caches := Caches.empty } ∧
      AStateInv pers st' := by
  rw [arena.core.drop_scratch] at hrun
  obtain ⟨s1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { s1 with store := e } := (Result.ok_injective hrun).symm
  subst hst
  rw [arena.core.flush_caches] at h1
  obtain ⟨c, hc, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  have hs1 : s1 = { st with caches := c } := (Result.ok_injective h1).symm
  subst hs1
  obtain ⟨hcr, hci⟩ := caches_reset hinv.caches hc
  obtain ⟨hsr, hsi⟩ := estore_drop hrel.store hinv.store he
  exact ⟨rfl,
    ⟨hsr, hrel.memos, hcr, hrel.pins, StoreWF'.dropScratch_wf hrel.storeWF⟩,
    ⟨hsi, hinv.memos, hci⟩⟩

/-- **THE BRIDGE** — `bracket_close` from the promote window: a bracket entered
at a boundary whose body delivered `Ext` from the opened store, and whose
promotion left the WEAK relation, closes to the STRONG relation, `Ext` from
the boundary, and the next boundary. -/
theorem bracket_close_w {pers st st' lst lst2}
    (hbr : BrOK lst) (hrel : AStateRelW pers st lst2) (hinv : AStateInv pers st)
    (hext : Ext lst.store.enableScratch lst2.store)
    (hdrop : arena.core.drop_scratch st = ok st') :
    (dropScratch : AM Unit).run lst2 = .ok ((), (brLeft lst2)) ∧
      AStateRel pers st' (brLeft lst2) ∧ AStateInv pers st' ∧
      Ext lst.store (brLeft lst2).store ∧ BrOK (brLeft lst2) := by
  obtain ⟨hr, hrel', hinv'⟩ := drop_scratch_refines_w hrel hinv hdrop
  exact ⟨hr, hrel', hinv', ext_bracket' hbr.closedStore hrel.storeWF hext,
    ⟨StoreWF'.dropScratch_wf hrel.storeWF, rfl⟩⟩

/-! ## The Inductives seam (task #97-P5-Checker's finding 14)

**Moved down from `Refine2/Checker/Top.lean` by task #97-P5-Checker-2.**  The
seam has to be declared BELOW the tier that discharges it: task #97-P5-Ind's
`ind_rel : IndRel` is unconditional (`Refine2/Inductives/Top.lean`), and
`Refine2/Checker/Top.lean`'s thirteen `hind : IndRel` binders can only go if
that file may *import* the proof.  So `IndRel` lives here — in the shared base
both `Refine2/Checker/**` and `Refine2/Inductives/**` already import — and
`Refine2/Checker/Top.lean` imports `Refine2/Inductives/Top.lean` instead of
the other way round.  Nothing about the statement changed. -/

/-- **`arena::inductives`'s obligation as the declaration checker's seam.**
The `.indDecl` arm of `check_decl` is the only place the declaration checker
reaches the inductive routes, and they are 6 705 lines of their own tier.
This is the seam in `KnotRel`'s shape: one clause, discharged by
`Refine2/Inductives/Top.lean`'s `ind_rel`. -/
structure IndRel : Prop where
  checkIndDecl : ∀ {pers st lst rf lf mode block n_p o},
    AStateRel pers st lst → AStateInv pers st →
    IFEnvRel rf lf → IFEnvInv rf →
    arena.inductives.check_ind_decl pers mode rf block n_p st = ok o →
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (ConRon.Arena.Inductives.checkIndDecl (ConRon.Refine.absMode mode) lf
        (absICIL block) (absU n_p))

/-! ## `arena::checker_split`'s seam datum -/

/-- `arena::checker_split::ValueKind`. -/
def absValueKind : arena.checker_split.ValueKind → ValueKind
  | .Defn => .defn
  | .Thm => .thm
  | .Opaque => .opaque

/-- `arena::checker_split::ValueGroup` — the datum that crosses the
install/check seam, and the one record of the declaration layer that is not in
`Refine2/AbsState.lean` (it belongs to `arena::checker_split`, not
`arena::env`). -/
def absValueGroup (g : arena.checker_split.ValueGroup) : ValueGroup :=
  ⟨absValueKind g.kind, absIConstantVal g.cv_a, absEIdx g.jv⟩

attribute [simp] absValueKind absValueGroup

/-- `arena::checker::PendingCheck` — a phase-A record awaiting its phase-B
check.  `vis` is the environment counter at the install; it is out of the
INDEX and into the record (task #97-P6-6b), which is why it abstracts as a
plain counter and not through `IFEnvRel`. -/
def absPendingCheck (p : arena.checker.PendingCheck) : PendingCheck :=
  ⟨absValueGroup p.vg, absU p.pos, absU p.vis⟩

def absPendingCheckL (v : alloc.vec.Vec arena.checker.PendingCheck) :
    List PendingCheck := v.val.map absPendingCheck
def absPendingCheckLFrom (v : alloc.vec.Vec arena.checker.PendingCheck)
    (i : Std.Usize) : List PendingCheck :=
  (v.val.drop i.val).map absPendingCheck

/-- `arena::nat_op_pin_set::INatOpPinSet` — one toolchain's `Nat`-operation
pins over handles.  The `toolchain` string is `Vec<u32>` code points against
the twin's `String` (DESIGN §3.3), which is `Refine/Abs.lean`'s `absString`
and holds on valid code points only — `StrWF` is the caller's obligation,
exactly as it is at `StrNode`. -/
def absINatOpPinSet (p : arena.nat_op_pin_set.INatOpPinSet) : INatOpPinSet :=
  ⟨ConRon.Refine.absString p.toolchain,
    absEIdx p.div_pin, absEIdx p.mod_pin, absEIdx p.gcd_pin, absEIdx p.land_pin,
    absEIdx p.lor_pin, absEIdx p.xor_pin, absEIdx p.shift_left_pin,
    absEIdx p.shift_right_pin,
    absEIdxL p.div_proofs, absEIdxL p.mod_proofs, absEIdxL p.gcd_proofs,
    absEIdxL p.land_proofs, absEIdxL p.lor_proofs, absEIdxL p.xor_proofs,
    absEIdxL p.shift_left_proofs, absEIdxL p.shift_right_proofs⟩

def absINatOpPinSetL (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) :
    List INatOpPinSet := v.val.map absINatOpPinSet
def absINatOpPinSetLFrom (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (i : Std.Usize) : List INatOpPinSet :=
  (v.val.drop i.val).map absINatOpPinSet

/-- `kernel::nat_op_pins::NatOpPinSet`'s well-formedness, as
`Refine/PinsAbs.lean`'s `absNatOpPinSet` needs it: every term and every
toolchain code point.  The pins are con-leche's own data, so
`Refine/Pins*.lean`'s decoder lemmas are where it is discharged. -/
def NatOpPinSetWF (p : kernel.nat_op_pins.NatOpPinSet) : Prop :=
  ConRon.Refine.StrWF p.toolchain ∧
    ConRon.Refine.ExprWF p.div_pin ∧ ConRon.Refine.ExprWF p.mod_pin ∧
    ConRon.Refine.ExprWF p.gcd_pin ∧ ConRon.Refine.ExprWF p.land_pin ∧
    ConRon.Refine.ExprWF p.lor_pin ∧ ConRon.Refine.ExprWF p.xor_pin ∧
    ConRon.Refine.ExprWF p.shift_left_pin ∧
    ConRon.Refine.ExprWF p.shift_right_pin ∧
    ConRon.Refine.ExprsWF p.div_proofs ∧ ConRon.Refine.ExprsWF p.mod_proofs ∧
    ConRon.Refine.ExprsWF p.gcd_proofs ∧ ConRon.Refine.ExprsWF p.land_proofs ∧
    ConRon.Refine.ExprsWF p.lor_proofs ∧ ConRon.Refine.ExprsWF p.xor_proofs ∧
    ConRon.Refine.ExprsWF p.shift_left_proofs ∧
    ConRon.Refine.ExprsWF p.shift_right_proofs

attribute [simp] absPendingCheck absPendingCheckL absPendingCheckLFrom
  absINatOpPinSet absINatOpPinSetL absINatOpPinSetLFrom

/-! ## The axiom census — rule 11's four, and the relation's weakening -/

/-- info: 'ConRon.Refine2.am_ite_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms am_ite_bind

/-- info: 'ConRon.Refine2.am_bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms am_bind_congr

/-- info: 'ConRon.Refine2.SimRel.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimRel.mono

/-- info: 'ConRon.Refine2.ifenv_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifenv_push_refines

/-- info: 'ConRon.Refine2.openPisAtFvarsF_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openPisAtFvarsF_length

end ConRon.Refine2

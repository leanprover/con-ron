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
import ConRon.Refine2.Dup
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

/-! ## `SimRel₀` — the lockstep `SimRel` (task #97-T2-LOCKSTEP)

`AOutRel`/`SimRel` over `AStateRel₀`, without `Ext` and without the dead
pre-state in the outcome.  `AOutRel`/`SimRel` above are **deprecated shims**
until every lane has moved; `SimRel.to₀` projects a proved old statement.  A
result that wants a well-formedness predicate states it inside `R`
(`fun r v => v = A r ∧ WF r`). -/

def AOutRel₀ {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ v lst', x = .ok (v, lst') ∧ R r v ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st'
  | .Err e => AErrSim e x

def SimRel₀ {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  AOutRel₀ R pers o.1 o.2 (x.run lst)

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

/-- **`arena::intern`'s memo**, the one memo of these two tiers keyed on a
con-leche VALUE rather than a handle.  `Refine/Expr.lean`'s `absExpr` is exact
on WELL-FORMED values only (task #97-P5-0's rule 4, and the reason `TblRel` is
`RelOn P` and not `Rel`), so `P` is `ExprWF` and the caller owes it — which
the pin modules discharge from `Refine/Pins*.lean`, every subject of
`arena::intern` being a con-leche pin. -/
def EMemoRel (rm : ron.hashmap2.HashMap2 kernel.expr.Expr arena.handle.EIdx)
    (lm : Std.HashMap ConLeche.Expr EIdx) : Prop :=
  RelOn ConRon.Refine.ExprWF rm lm ConRon.Refine.absExpr absEIdx ∧
    Inv kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable rm ∧
    ConRon.Refine.HashMap2.KeysOk ConRon.Refine.ExprWF rm

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

def absLevelLFrom (v : alloc.vec.Vec kernel.level.Level) (i : Std.Usize) :
    List ConLeche.Level := (v.val.drop i.val).map ConRon.Refine.absLevel
def absNameLFrom (v : alloc.vec.Vec kernel.name.Name) (i : Std.Usize) :
    List ConLeche.Name := (v.val.drop i.val).map ConRon.Refine.absName
def absBasisKindLFrom (v : alloc.vec.Vec kernel.env.BasisKind) (i : Std.Usize) :
    List ConLeche.BasisKind := (v.val.drop i.val).map ConRon.Refine.absBasisKind

attribute [simp] absNIdxL absEIdxL absLIdxL absNIdxLFrom absEIdxLFrom absLIdxLFrom
  absIRecRuleL absIRecRuleLFrom absICIL absICILFrom absIDeclL absStmts
  absStmtsFrom absEqPairs absEqPairsFrom absLevelLFrom absNameLFrom absBasisKindLFrom
/-! ## The environment layer's own invariant
`Refine2/AbsState.lean`'s relations read a Rust map through `HashMap2.toFun`,
which specifies a well-formed table and says nothing about a malformed one;
every other `RelOn` of this tower is paired with an `Inv` in `AStateInv`, and
the environment is not in the state, so its `Inv` travels with it
(`IFEnvInv`).  Its range clauses are what let a push at the end of a list move
no row: `ifenv_push` stores the length before its `push`, `ifenv_pop_temp` puts
back a row it took out, and there is no other writer. -/
theorem IFEnvInv.idxInv {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rf.idx := h.1

/-- **Every slot the index stores is in range of the constant list**, so an
append does not change what an old row reads. -/
theorem IFEnvInv.idxRange {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    ∀ n s, ConRon.Refine.HashMap2.toFun rf.idx n = some s →
      s.val < rf.env.consts.val.length :=
  h.2.1

/-- The table map's `Inv`. -/
theorem IFEnvInv.tblInv {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rf.tbls := h.2.2.1

/-- Every slot the table map stores is in range of `env.tables`. -/
theorem IFEnvInv.tblRange {rf : arena.env.IFEnv} (h : IFEnvInv rf) :
    ∀ n s, ConRon.Refine.HashMap2.toFun rf.tbls n = some s →
      s.val < rf.env.tables.val.length :=
  h.2.2.2

/-! ## The environment relation a fold carries

Every statement of this tier takes `hfe : IFEnvRel pers rf lf` **and**
`hfinv : IFEnvInv rf`, and a fold feeds its step's answer back into the step,
so the result relation of every `IFEnv`-returning statement is the pair. -/

/-- **The environment, related and well formed** — the result relation a fold
step has to carry. -/
def IFEnvRelI (pers : arena.store.PersTier) (rf : arena.env.IFEnv) (lf : IFEnv) : Prop :=
  IFEnvRel pers rf lf ∧ IFEnvInv rf

theorem IFEnvRelI.rel {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (h : IFEnvRelI pers rf lf) : IFEnvRel pers rf lf := h.1

theorem IFEnvRelI.inv {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (h : IFEnvRelI pers rf lf) : IFEnvInv rf := h.2

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
    dupId_nidx _ _ h]

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

/-- **`ifenv_push` ⊑ `IFEnv.push`, relation and invariant together.**  The port
writes the index row at the constant list's CURRENT length and appends, where the
twin conses onto a newest-first list and inserts the constant itself: at the pushed
name the grown list's slot is the pushed constant, and every other row's slot was in
range already (`IFEnvInv.idxRange`), so the append does not change what it reads.
The base and the tables are untouched. -/
theorem ifenv_push_refines {pers : arena.store.PersTier} {rf rf' : arena.env.IFEnv} {lf : IFEnv}
    {ci : arena.env.IConstantInfo}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (h : arena.env.ifenv_push rf ci = ok rf') :
    IFEnvRel pers rf' (lf.push (absIConstantInfo ci)) ∧ IFEnvInv rf' := by
  rw [arena.env.ifenv_push] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hsv : s.val = rf.env.consts.val.length := by
    simp only [lift, Result.ok.injEq] at hs
    subst hs
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  obtain ⟨hinv', -, hupd, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
      hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hvv : v.val = rf.env.consts.val ++ [ci] := ConRon.Refine.vec_push_val hv
  have hrf' : rf' = { rf with env := { rf.env with consts := v }, idx := q.2 } :=
    (Result.ok_injective h).symm
  subst hrf'
  have hname : absNIdx n = (absIConstantInfo ci).name := i_constant_info_name_abs hn
  refine ⟨⟨⟨?_, hfe.tbls, hfe.base, hfe.below, hfe.belowRec, hfe.baseOK⟩, ?_⟩,
    hinv', ?_, hfinv.tblInv, hfinv.tblRange⟩
  · -- the own index
    intro m
    simp only [ownRow, hupd]
    simp only [IFEnv.push, _root_.Std.HashMap.getElem?_insert, Function.update_apply]
    by_cases hm : m = n
    · subst hm
      rw [ite_eq_left rfl, ite_eq_left (by simp [hname])]
      simp only [hvv, Option.bind_some]
      rw [List.getElem?_append_right (by omega), hsv, Nat.sub_self]
      simp
    · rw [ite_eq_right hm]
      have hne : ¬ ((absIConstantInfo ci).name == absNIdx m) = true := by
        simp only [beq_iff_eq]
        intro hc
        exact hm (absNIdx_inj (hc.symm.trans hname.symm))
      rw [ite_eq_right hne, ← hfe.idx m, ownRow]
      cases hp : ConRon.Refine.HashMap2.toFun rf.idx m with
      | none => rfl
      | some p =>
        simp only [hvv, Option.bind_some]
        rw [List.getElem?_append_left (hfinv.idxRange m p hp)]
  · -- the constant list
    show (lf.push (absIConstantInfo ci)).env = absIEnv _
    simp only [IFEnv.push, absIEnv, hvv, List.map_append, List.reverse_append]
    rw [hfe.env]
    simp [absIEnv]
  · -- every stored slot still in range
    intro m p hp
    rw [hupd, Function.update_apply] at hp
    show p.val < v.val.length
    rw [hvv]
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hm : m = n
    · subst hm
      rw [ite_eq_left rfl] at hp
      obtain rfl : p = s := (Option.some_injective _ hp).symm
      omega
    · rw [ite_eq_right hm] at hp
      have := hfinv.idxRange m p hp
      omega

/-- **`ifenv_push_table` ⊑ `IFEnv.pushTable`, relation and invariant
together** — `ifenv_push_refines` at the table map.  The constants, the index and
the base are untouched. -/
theorem ifenv_push_table_refines {pers : arena.store.PersTier} {rf rf' : arena.env.IFEnv} {lf : IFEnv}
    {t : arena.env.IProjTable}
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (h : arena.env.ifenv_push_table rf t = ok rf') :
    IFEnvRel pers rf' (lf.pushTable (absIProjTable t)) ∧ IFEnvInv rf' := by
  rw [arena.env.ifenv_push_table] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := dupId_nidx _ _ hn
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hsv : s.val = rf.env.tables.val.length := by
    simp only [lift, Result.ok.injEq] at hs
    subst hs
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  obtain ⟨hinv', -, hupd, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
      hfinv.tblInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hvv : v.val = rf.env.tables.val ++ [t] := ConRon.Refine.vec_push_val hv
  have hrf' : rf' = { rf with env := { rf.env with tables := v }, tbls := q.2 } :=
    (Result.ok_injective h).symm
  subst hrf'
  refine ⟨⟨⟨hfe.idx, ?_, hfe.base, hfe.below, hfe.belowRec, hfe.baseOK⟩, ?_⟩,
    hfinv.idxInv, hfinv.idxRange, hinv', ?_⟩
  · -- the table map
    intro m
    simp only [ownTbl, hupd]
    simp only [IFEnv.pushTable, _root_.Std.HashMap.getElem?_insert, Function.update_apply]
    by_cases hm : m = t.struct_name
    · subst hm
      rw [ite_eq_left rfl, ite_eq_left (by simp [absIProjTable])]
      simp only [hvv, Option.bind_some]
      rw [List.getElem?_append_right (by omega), hsv, Nat.sub_self]
      simp
    · rw [ite_eq_right hm, ite_eq_right (by
        simp only [absIProjTable, beq_iff_eq]; intro h; exact hm (absNIdx_inj h).symm),
        ← hfe.tbls m, ownTbl]
      cases hp : ConRon.Refine.HashMap2.toFun rf.tbls m with
      | none => rfl
      | some p =>
        simp only [hvv, Option.bind_some]
        rw [List.getElem?_append_left (hfinv.tblRange m p hp)]
  · -- the table list
    show (lf.pushTable (absIProjTable t)).env = absIEnv _
    have h := hfe.env
    simp only [IFEnv.pushTable, absIEnv, hvv, List.map_append, List.reverse_append] at h ⊢
    rw [h]
    simp
  · -- every stored slot still in range
    intro m p hp
    rw [hupd, Function.update_apply] at hp
    show p.val < v.val.length
    rw [hvv]
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hm : m = t.struct_name
    · subst hm
      rw [ite_eq_left rfl] at hp
      obtain rfl : p = s := (Option.some_injective _ hp).symm
      omega
    · rw [ite_eq_right hm] at hp
      have := hfinv.tblRange m p hp
      omega

/-! ## Peeling a twin bind

`am_run_bind_ok` is the `ok` half of `Core/Induction.lean`'s `am_run_bind`,
which is a sibling of this file rather than below it, hence the second
spelling. -/

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

/-- The ambient Rust state with its store replaced: what a `&mut EStore`
function hands back, read as an `AState`. -/
@[reducible] def withStore (rst : arena.monad.AState) (e : arena.store.EStore) :
    arena.monad.AState := { rst with store := e }

/-- `arena::nat_op_pin_set::INatOpPinSet` — one toolchain's `Nat`-operation
pins over handles.  The `toolchain` string is `Vec<u32>` code points against
the twin's `String` (DESIGN §3.3), which is `Refine/Abs.lean`'s `absString`
and holds on valid code points only — `StrWF` is the caller's obligation,
exactly as it is at `StrNode`. -/
def absTypePinsI (v : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx)) :
    List (NIdx × EIdx) :=
  v.val.map fun q => (absNIdx q.1, absEIdx q.2)

def absINatOpPinSet (p : arena.nat_op_pin_set.INatOpPinSet) : INatOpPinSet :=
  ⟨ConRon.Refine.absString p.toolchain,
    absEIdx p.div_pin, absEIdx p.mod_pin, absEIdx p.gcd_pin, absEIdx p.land_pin,
    absEIdx p.lor_pin, absEIdx p.xor_pin, absEIdx p.shift_left_pin,
    absEIdx p.shift_right_pin,
    absEIdxL p.div_proofs, absEIdxL p.mod_proofs, absEIdxL p.gcd_proofs,
    absEIdxL p.land_proofs, absEIdxL p.lor_proofs, absEIdxL p.xor_proofs,
    absEIdxL p.shift_left_proofs, absEIdxL p.shift_right_proofs,
    absTypePinsI p.div_type_pins, absTypePinsI p.mod_type_pins,
    absTypePinsI p.gcd_type_pins, absTypePinsI p.land_type_pins,
    absTypePinsI p.lor_type_pins, absTypePinsI p.xor_type_pins,
    absTypePinsI p.shift_left_type_pins, absTypePinsI p.shift_right_type_pins⟩

def absINatOpPinSetL (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) :
    List INatOpPinSet := v.val.map absINatOpPinSet
def absINatOpPinSetLFrom (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (i : Std.Usize) : List INatOpPinSet :=
  (v.val.drop i.val).map absINatOpPinSet

/-- A type-pin list's well-formedness: every name and every type. -/
def TypePinsWF (v : alloc.vec.Vec (kernel.name.Name × kernel.expr.Expr)) : Prop :=
  ∀ q ∈ v.val, ConRon.Refine.NameWF q.1 ∧ ConRon.Refine.ExprWF q.2

/-- `kernel::nat_op_pins::NatOpPinSet`'s well-formedness, as
`Refine/PinsAbs.lean`'s `absNatOpPinSet` needs it: every term, every name
and every toolchain code point.  The pins are con-leche's own data, so
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
    ConRon.Refine.ExprsWF p.shift_right_proofs ∧
    TypePinsWF p.div_type_pins ∧ TypePinsWF p.mod_type_pins ∧
    TypePinsWF p.gcd_type_pins ∧ TypePinsWF p.land_type_pins ∧
    TypePinsWF p.lor_type_pins ∧ TypePinsWF p.xor_type_pins ∧
    TypePinsWF p.shift_left_type_pins ∧ TypePinsWF p.shift_right_type_pins
attribute [simp] absTypePinsI absINatOpPinSet absINatOpPinSetL
  absINatOpPinSetLFrom

/-! ## The axiom census — rule 11's four, and the relation's weakening -/

/-- info: 'ConRon.Refine2.am_ite_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms am_ite_bind

/-- info: 'ConRon.Refine2.am_bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms am_bind_congr

/-- info: 'ConRon.Refine2.ifenv_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifenv_push_refines

/-- info: 'ConRon.Refine2.ifenv_push_table_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifenv_push_table_refines

end ConRon.Refine2

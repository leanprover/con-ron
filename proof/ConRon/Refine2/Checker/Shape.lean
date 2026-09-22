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
import ConRon.Arena.Promote

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun sl_v)

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
  absExprLFrom absCIListFrom absRecRuleLFrom absDeclLFrom absLevelLFrom
  absNameLFrom absBasisKindLFrom

/-! ## The environment index's own invariant

`Refine2/AbsState.lean`'s `IFEnvRel` reads the Rust index through
`HashMap2.toFun`, which is a specification of a well-formed table and says
nothing about a malformed one.  Every other `RelOn` of this tower is paired
with an `Inv` in `AStateInv`; the environment is not in the state, so its
`Inv` travels with it. -/
def IFEnvInv (rf : arena.env.IFEnv) : Prop :=
  Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rf.idx

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

end ConRon.Refine2

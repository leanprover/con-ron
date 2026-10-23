/-
# `ConRon.Bridge.Core.Walks.PropRead` — the head-symbol prop-ness readers

`Arena/PropRead.lean` is nine state-only readers (`peelNeverPis`, `numArgs`,
`residualPW`, `headTypePW`, `typeSortPW`, `headProofPW`, `proofPW`,
`notProofFast`, `isProofFast`), shaped as `Walks/Nat.lean`'s walks: no knot,
no fuel on the pure side, each an EQUATION with the con-leche function of the same name at
`find? := env.find?`.  This module is that, then the three walks that
stand on it (`propIrrel`, `annotPwPi`, `annotPwLam`).

## The shape

* **The three view-only readers** (`peelNeverPis`, `numArgs`, `residualPW`)
  leave the state alone: `s' = s₀`.
* **The four that read a constant's stored type** (`headTypePW`,
  `typeSortPW`, `headProofPW`, `proofPW`) and the two arms above them may
  run `readNamesM` / `readLevelsM`, which move the two readback memos — so
  their postcondition is `CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
  s'.pins = s₀.pins`, the frame `Walks/Frame.lean`'s `ReadbackFrame`
  delivers.  The store EQUATION is stronger than `Ext` and is what these
  readers actually satisfy (nothing is interned: `toConstantVal` is pure off
  a projection table, and the tower guard keeps the readers off that arm).
* **Every reader is stated in ANSWER shape**: each one is reached, inside
  this file or from a caller, through another call's answer (`getAppFn`'s
  head, `peelPisW`'s residual, `toConstantVal`'s stored type, the knot's
  `whnfCore` answers).  None carries well-scopedness: the readers look at
  head shape only.

## The index lookup

`fe.find? I` against `env.find? nm` is `Bridge/Grind.lean` §8's `IndexAt`:
a hit's tower-ness is the denotation's, and off the tower the stored record
denotes the environment's; the arena's monadic `toConstantVal` is then pure
(``).
The has-parameters cutoff (DESIGN, task #97-P6-10) is con-leche's own
`Level.substPW_eq_self`.

## The proofs

Every reader is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`.  The readers are stated with their answer
as an EQUATION through `Option.map` of the con-leche function at whatever the
subject denotes (`(denoteE s₀.store h).map (Expr.binderDom k) = …`), or at a
given denotation where the caller names it (`headTypePW_specX`,
`headProofPW_specX`); con-leche's functions are each ONE equation over tags
and projections, passed locally to the walk that unfolds them (they are
recursive, so a registered rule would unfold them at every call); the
`view*` projections are facts keyed by the projection and the denotation
(`BindAt`, `AppAt`, …); the index at a constant is `Bridge/Grind.lean` §8's
`IndexAt`.  `substPWAt`'s cutoff and `rawNatLit?`'s literal arm
meet the same `grind` limitation (`_tmp/corpus/vcgen-grind/
nested-ctor-fallthrough-hyp.lean`) and the same workaround: `vcgen` runs on
the twin with the nested pattern as a `Bool` test (`substPWAt_split`).
-/
import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Facts the readers need and no tier had -/

/-- con-leche: none — a handle whose view is not a `.sort` denotes no sort. -/
theorem denote_not_sort {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ u, v = .sort u → False) : ∀ l, e ≠ .sort l := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => exact absurd rfl (hne u)
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — a handle whose view is not a `.lam` denotes no λ. -/
theorem denote_not_lam {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b, v = .lam ty b → False) : ∀ p q, e ≠ .lam p q := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b => exact absurd rfl (hne ty b)
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: ConLeche/Kernel/Level.lean:203-205 Level.substPW — **the
cutoff** of the arena's `substPWAt` (DESIGN, task #97-P6-10): a datum that names no
parameter (`never`, or `ifAllZero []`) is its own substitution, so answering
`pw` without the two readbacks is con-leche's `map`. -/
theorem substPW_cutoff {ks : List ConLeche.Name} {vs : List Level}
    {pw : PropWhen} (h : ∀ a as, pw ≠ .ifAllZero (a :: as)) :
    Level.substPW ks vs pw = pw := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons a as => exact absurd rfl (h a as)

/-- con-leche: none — **a `pure` exit** at a pinned state. -/
theorem triple_pureR {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => s = s₀⦄ (pure v : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  vcgen
  subst_vars; exact h

/-- con-leche: none — `viewConstName` reads the store and moves nothing. -/
theorem viewConstName_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewConstName h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewConstName h; ⊤⦄ := by
  vcgen [viewConstName] with finish

/-- con-leche: none — a denoting handle list read at an index with a
denoting default. -/
theorem denoteEList_getD {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ (i : Nat) (e : EIdx) (x : Expr), denoteE st e = some x →
        denoteE st (hs.getD i e) = some (xs.getD i x)
  | [], xs, h, i, e, x, hx => by rw [denoteEList_nil_inv h]; simpa using hx
  | a :: as, xs, h, i, e, x, hx => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteEList_cons_inv h
    cases i with
    | zero => simpa using hy
    | succ i => simpa using denoteEList_getD hys i e x hx

/-! ## The readers' vocabulary

The `view*` projections the readers read are `Bridge/Grind.lean` §6's
(`view_of_view*`, guarded at the read).  Here: a stored
projection entry's body; a handle list read at an index; the readbacks at the
tier's invariant. -/

/-- con-leche: none — a handle list read at an index, with a default. -/
def GetDAt (st : EStore) (hs : List EIdx) (i : Nat) (e : EIdx) :
    Option (List Expr) → Option Expr → Prop
  | some xs, some x => denoteE st (hs.getD i e) = some (xs.getD i x)
  | _, _ => True

/-- con-leche: none — `denoteEList_getD` at the read. -/
theorem getDAt (st : EStore) (hs : List EIdx) (i : Nat) (e : EIdx) :
    GetDAt st hs i e (Frontend.denoteEList st hs) (denoteE st e) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs =>
  cases hx : denoteE st e with
  | none => trivial
  | some x => exact denoteEList_getD h i e x hx
grind_pattern [bridge_grind] getDAt => List.getD hs i e, Frontend.denoteEList st hs, denoteE st e

/-- con-leche: none — `GetDAt` at a denoting list and default. -/
theorem GetDAt.some {st : EStore} {hs : List EIdx} {i : Nat} {e : EIdx} {xs : List Expr}
    {x : Expr} (H : GetDAt st hs i e (some xs) (some x)) :
    denoteE st (hs.getD i e) = some (xs.getD i x) := H
grind_pattern [bridge_grind] GetDAt.some => GetDAt st hs i e (some xs) (some x)

/-- con-leche: none — a stored projection entry's body denotes the entry's. -/
def EntryAt (st : EStore) (en : IProjEntry) : Option ProjEntry → Prop
  | some p => denoteE st en.body = some p.body
  | none => True

/-- con-leche: none — `denoteProjEntry`'s body field, at the denotation. -/
theorem entryAt (st : EStore) (en : IProjEntry) : EntryAt st en (denoteProjEntry st en) := by
  cases h : denoteProjEntry st en with
  | none => trivial
  | some p =>
    simp only [denoteProjEntry] at h
    split at h
    · split at h
      · rename_i b _ _ hb _ _
        cases h; exact hb
      · simp at h
    · simp at h
grind_pattern [bridge_grind] entryAt => denoteProjEntry st en

/-- con-leche: none — a projection entry, or a default. -/
def projOf : Option ProjEntry → ProjEntry | some p => p | none => default

/-- con-leche: none — the index's projection-table answer against the
environment's: found together, and a found entry's body denotes. -/
def ProjFound (st : EStore) : Option IProjEntry → Option ProjEntry → Prop
  | some en, some p => denoteE st en.body = some p.body
  | none, none => True
  | _, _ => False

/-- con-leche: none — `ProjFound` at a found entry: the environment found one
too, and its body is the entry's. -/
theorem ProjFound.some {st : EStore} {en : IProjEntry} {o : Option ProjEntry}
    (H : ProjFound st (some en) o) :
    o = some (projOf o) ∧ denoteE st en.body = some (projOf o).body := by
  cases o with
  | none => exact H.elim
  | some p => exact ⟨rfl, H⟩
grind_pattern [bridge_grind] ProjFound.some => ProjFound st (some en) o

/-- con-leche: none — `ProjFound` at a miss: the environment missed too. -/
theorem ProjFound.none {st : EStore} {o : Option ProjEntry} (H : ProjFound st none o) :
    o = none := by
  cases o with
  | none => rfl
  | some p => exact H.elim
grind_pattern [bridge_grind] ProjFound.none => ProjFound st none o

/-- con-leche: none — `readNamesM` at the tier's invariant (`CheckOK.ofReadbackFrame`). -/
theorem readNamesM_specC (s₀ : AState) (hs : List NIdx) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ readNamesM hs
    ⦃fun xs s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        Frontend.denoteNList s₀.store.ns hs = some xs; ⊤⦄ :=
  triple_mono (readNamesM_spec s₀ hs hok.caches.readN)
    (fun _ _ ⟨hst, hm, hp, hc, hd, hN⟩ =>
      ⟨CheckOK.ofReadbackFrame hok (ReadbackFrame.ofReadN hst hm hp hc hN), hst, hp, hd⟩)

/-- con-leche: none — `readLevelsM` at the tier's invariant. -/
theorem readLevelsM_specC (s₀ : AState) (h : LsIdx) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ readLevelsM h
    ⦃fun us s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        denoteLs s₀.store.lss h = some us; ⊤⦄ :=
  triple_mono (readLevelsM_spec s₀ h hok.caches.readLs)
    (fun _ _ ⟨hst, hm, hp, hc, hd, hLs⟩ =>
      ⟨CheckOK.ofReadbackFrame hok (ReadbackFrame.ofReadLs hst hm hp hc hLs), hst, hp, hd⟩)

/-! ### `Option` readings of con-leche's answers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:204-209 notProofFast — its verdict
at a datum. -/
def notPW : Option PropWhen → Bool | some pw => !pw.isProp | none => false
/-- con-leche: ConLeche/Kernel/PropRead.lean:211-216 isProofFast — its verdict at
a datum. -/
def isPW : Option PropWhen → Bool | some pw => pw.isProp | none => false
/-- con-leche: ConLeche/Kernel/PropRead.lean:164-176 headProofPW — the
projection arm's answer at a datum: never-a-proposition only. -/
def neverOnly : Option PropWhen → Option PropWhen
  | some pw => if pw.isNever then some pw else none
  | none => none
attribute [bridge_grind =] notPW isPW neverOnly

/-- con-leche: none — does a datum name a level parameter (the twin's
`substPWAt` cutoff as a `Bool`). -/
def pwHasParams : PropWhen → Bool | .ifAllZero (_ :: _) => true | _ => false

/-- con-leche: ConLeche/Kernel/Level.lean substPW — the cutoff as an
equation: a datum naming no parameter is its own substitution. -/
theorem substPW_of_noParams {ks : List ConLeche.Name} {vs : List Level} {pw : PropWhen}
    (h : pwHasParams pw = false) : Level.substPW ks vs pw = pw :=
  substPW_cutoff (fun a as he => by subst he; simp [pwHasParams] at h)
grind_pattern [bridge_grind] substPW_of_noParams => Level.substPW ks vs pw

/-! ## 2. con-leche's readers as equations over tags and projections

One equation per function (per arm of its structural argument); each is
recursive, so each is passed to the walk that unfolds it, not registered. -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:50-54 Expr.binderDom — the
outermost binder's domain. -/
theorem binderDom_zero_eq (x : Expr) : x.binderDom 0 =
    if exprTag x = ETag.forallE then some (exprBinderType x) else none := by
  cases x <;> simp [Expr.binderDom, exprTag, exprBinderType, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:50-54 Expr.binderDom — one binder
deeper. -/
theorem binderDom_succ_eq (k : Nat) (x : Expr) : x.binderDom (k + 1) =
    if exprTag x = ETag.forallE then (exprBody x).binderDom k else none := by
  cases x <;> simp [Expr.binderDom, exprTag, exprBody, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — one
application deeper. -/
theorem numArgs_eq (x : Expr) : x.numArgs =
    if exprTag x = ETag.app then (exprFn x).numArgs + 1 else 0 := by
  cases x <;> simp [Expr.numArgs, exprTag, exprFn, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — at a present
residual. -/
theorem residualPW_some_eq (x : Expr) : ConLeche.residualPW (some x) =
    if exprTag x = ETag.sort then some (Level.zeronessOf (exprSort x)) else none := by
  cases x <;> simp [ConLeche.residualPW, exprTag, exprSort, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — no residual. -/
theorem residualPW_none_eq : ConLeche.residualPW none = none := rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-79 lamProj? — one λ deeper. -/
theorem lamProj?_eq (k : Nat) (x : Expr) : ConLeche.lamProj? k x =
    if exprTag x = ETag.lam then ConLeche.lamProj? (k + 1) (exprBody x)
    else if exprTag x = ETag.bvar then
      (if exprBVar x < k then some (k, exprBVar x) else none)
    else none := by
  cases x <;> simp [ConLeche.lamProj?, exprTag, exprBody, exprBVar, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: none — the arity of a `lamProj?` answer. -/
def lpK : Option (Nat × Nat) → Nat | some (k, _) => k | none => 0
/-- con-leche: none — the projected index of a `lamProj?` answer. -/
def lpJ : Option (Nat × Nat) → Nat | some (_, j) => j | none => 0
attribute [bridge_grind =] lpK lpJ

/-- con-leche: ConLeche/Kernel/PropRead.lean:81-97 unwrapIdDefs — one
unwrapping: an applied identity-like definition at its arity unfolds to the
argument it projects. -/
theorem unwrapIdDefs_succ_eq (f : ConLeche.Name → Option ConstantInfo) (n : Nat) (e : Expr) :
    ConLeche.unwrapIdDefs f (n + 1) e =
      if exprTag e.getAppFn = ETag.const ∧ cDefn? (f (exprConstName e.getAppFn)) = true ∧
          (ConLeche.lamProj? 0 (cDefnValue (f (exprConstName e.getAppFn)))).isSome = true ∧
          (lpK (ConLeche.lamProj? 0 (cDefnValue (f (exprConstName e.getAppFn)))) ≤
              e.getAppArgs.length &&
            e.getAppArgs.length ==
              lpK (ConLeche.lamProj? 0 (cDefnValue (f (exprConstName e.getAppFn))))) = true
      then ConLeche.unwrapIdDefs f n (e.getAppArgs.getD
        (lpK (ConLeche.lamProj? 0 (cDefnValue (f (exprConstName e.getAppFn)))) - 1 -
          lpJ (ConLeche.lamProj? 0 (cDefnValue (f (exprConstName e.getAppFn))))) e)
      else e := by
  simp only [ConLeche.unwrapIdDefs]
  generalize e.getAppFn = g
  cases g <;> simp [exprTag, ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]
  rename_i c us
  simp only [exprConstName]
  cases hf : f c with
  | none => simp [cDefn?]
  | some ci =>
    cases ci <;> simp [cDefn?, cDefnValue]
    rename_i cv v h
    cases hl : ConLeche.lamProj? 0 v with
    | none => simp
    | some p => obtain ⟨k, j⟩ := p; simp [lpK, lpJ]

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — at no binder:
the unwrapping. -/
theorem peelPisW_zero_eq (f : ConLeche.Name → Option ConstantInfo) (e : Expr) :
    ConLeche.peelPisW f 0 e = some (ConLeche.unwrapIdDefs f 4 e) := by
  simp [ConLeche.peelPisW]

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — one binder: a
`∀`, or a `∀` once unwrapped. -/
theorem peelPisW_succ_eq (f : ConLeche.Name → Option ConstantInfo) (k : Nat) (e : Expr) :
    ConLeche.peelPisW f (k + 1) e =
      if exprTag e = ETag.forallE then ConLeche.peelPisW f k (exprBody e)
      else if exprTag (ConLeche.unwrapIdDefs f 4 e) = ETag.forallE then
        ConLeche.peelPisW f k (exprBody (ConLeche.unwrapIdDefs f 4 e))
      else none := by
  cases e with
  | forallE t b => simp [ConLeche.peelPisW, exprTag, exprBody]
  | _ =>
    simp only [ConLeche.peelPisW]
    generalize ConLeche.unwrapIdDefs f 4 _ = u
    cases u <;> simp [exprTag, exprBody, ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:112-131 headTypePW — the head
reader as ONE equation over tags and projections (the lookup through
`cValP`). -/
theorem headTypePW_eq (f : ConLeche.Name → Option ConstantInfo) (r : Expr) (d : Nat)
    (x : Expr) (n : Nat) : ConLeche.headTypePW f r d x n =
      if exprTag x = ETag.const then
        (if (f (exprConstName x)).isSome = true ∧
            (exprConstLevels x).length = (cValP (f (exprConstName x))).levelParams.length then
          (ConLeche.residualPW (ConLeche.peelPisW f n (cValP (f (exprConstName x))).type)).map
            (Level.substPW (cValP (f (exprConstName x))).levelParams (exprConstLevels x))
        else none)
      else if exprTag x = ETag.fvar then
        ConLeche.residualPW (ConLeche.peelPisW f n (exprFVarType x))
      else if exprTag x = ETag.bvar then
        (if exprBVar x < d then
          ConLeche.residualPW ((r.binderDom (d - 1 - exprBVar x)).bind (ConLeche.peelPisW f n))
        else none)
      else none := by
  cases x with
  | const I us =>
    simp only [ConLeche.headTypePW, exprTag, exprConstName, exprConstLevels, ite_true]
    cases hf : f I with
    | none => simp [cValP]
    | some ci => simp [cValP]
  | fvar k ty =>
    simp [ConLeche.headTypePW, exprTag, exprFVarType, ETag.fvar, ETag.const]
  | bvar i =>
    simp only [ConLeche.headTypePW, exprTag, exprBVar]
    simp only [ETag.bvar, ETag.const, ETag.fvar]
    by_cases hi : i < d
    · simp only [hi, ite_true]
      cases r.binderDom (d - 1 - i) <;> rfl
    · simp [hi]
  | _ => simp [ConLeche.headTypePW, exprTag, ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:136-140 typeSortPWGo — one step of
the telescope walk. -/
theorem typeSortPWGo_eq (f : ConLeche.Name → Option ConstantInfo) (r x : Expr) (d : Nat) :
    ConLeche.typeSortPWGo f r x d =
      if exprTag x = ETag.forallE then ConLeche.typeSortPWGo f r (exprBody x) (d + 1)
      else if exprTag x = ETag.sort then some .never
      else ConLeche.headTypePW f r d x.getAppFn x.numArgs := by
  cases x <;> simp [ConLeche.typeSortPWGo, exprTag, exprBody, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — the
projection arm through `Env.findProj?` (the table, the field-count test, the
entry), as a rewrite rule. -/
theorem headProofPW_proj {S : ConLeche.Name} {i : Nat} {e : Expr} :
    ConLeche.headProofPW env.find? env.findTable? (.proj S i e) =
      match env.findProj? S i with
      | some p =>
        (match ConLeche.typeSortPW env.find? p.body with
          | some pw => if pw.isNever then some pw else none
          | none => none)
      | none => none := by
  simp only [ConLeche.headProofPW, ConLeche.Env.findProj?]
  cases env.findTable? S with
  | none => rfl
  | some tbl =>
    by_cases hi : i < tbl.numFields
    · simp only [hi, ite_true]; rfl
    · simp only [hi, ite_false]

/-- con-leche: ConLeche/Kernel/PropRead.lean:164-176 headProofPW — the
projection arm at the projection entry. -/
def projPW (f : ConLeche.Name → Option ConstantInfo) : Option ProjEntry → Option PropWhen
  | some p => neverOnly (ConLeche.typeSortPW f p.body)
  | none => none
attribute [bridge_grind =] projPW

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — the term
head reader as ONE equation over tags and projections, at the environment's
lookup (the projection arm through `Env.findProj?`, `headProofPW_proj`). -/
theorem headProofPW_eq (x : Expr) : ConLeche.headProofPW env.find? env.findTable? x =
    if exprTag x = ETag.const then
      (if (env.find? (exprConstName x)).isSome = true ∧
          (exprConstLevels x).length =
            (cValP (env.find? (exprConstName x))).levelParams.length then
        (ConLeche.typeSortPW env.find? (cValP (env.find? (exprConstName x))).type).map
          (Level.substPW (cValP (env.find? (exprConstName x))).levelParams (exprConstLevels x))
      else none)
    else if exprTag x = ETag.fvar then ConLeche.typeSortPW env.find? (exprFVarType x)
    else if exprTag x = ETag.sort ∨ exprTag x = ETag.forallE ∨ exprTag x = ETag.lit then
      some .never
    else if exprTag x = ETag.proj then
      projPW env.find? (env.findProj? (exprProjName x) (exprProjIdx x))
    else none := by
  cases x with
  | const I us =>
    simp only [ConLeche.headProofPW, exprTag, exprConstName, exprConstLevels, ite_true]
    cases hf : env.find? I with
    | none => simp [cValP]
    | some ci => simp [cValP]
  | proj S i e =>
    rw [headProofPW_proj]
    simp only [exprTag, exprProjName, exprProjIdx, ETag.proj, ETag.const, ETag.fvar,
      ETag.sort, ETag.forallE, ETag.lit]
    simp only [projPW]
    cases env.findProj? S i with
    | none => simp
    | some p =>
      simp only [neverOnly]
      cases ConLeche.typeSortPW env.find? p.body <;> simp
  | _ => simp [ConLeche.headProofPW, exprTag, exprFVarType, ETag.forallE, ETag.bvar,
      ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:185-196 proofPW — one step:
through a λ, a `let` or an application, else the head. -/
theorem proofPW_eq (f : ConLeche.Name → Option ConstantInfo)
    (g : ConLeche.Name → Option ProjTable) (x : Expr) :
    ConLeche.proofPW f g x =
      if exprTag x = ETag.lam then ConLeche.proofPW f g (exprBody x)
      else if exprTag x = ETag.letE then ConLeche.proofPW f g (exprBody x)
      else if exprTag x = ETag.app then ConLeche.proofPW f g (exprFn x)
      else ConLeche.headProofPW f g x := by
  cases x <;> simp [ConLeche.proofPW, exprTag, exprBody, exprFn, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:204-209 notProofFast — at the
datum. -/
theorem notProofFast_eq (f : ConLeche.Name → Option ConstantInfo)
    (g : ConLeche.Name → Option ProjTable) (x : Expr) :
    ConLeche.notProofFast f g x = notPW (ConLeche.proofPW f g x) := by
  unfold ConLeche.notProofFast; cases ConLeche.proofPW f g x <;> rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:211-216 isProofFast — at the
datum. -/
theorem isProofFast_eq (f : ConLeche.Name → Option ConstantInfo)
    (g : ConLeche.Name → Option ProjTable) (x : Expr) :
    ConLeche.isProofFast f g x = isPW (ConLeche.proofPW f g x) := by
  unfold ConLeche.isProofFast; cases ConLeche.proofPW f g x <;> rfl

/-! ## 3. The view-only readers

`peelPis` is `Walks/Proj.lean`'s `peelPis_spec` (the recursor's and the
projection certificate's arity read it too). -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:50-54 Expr.binderDom — **THEOREM
1 for `binderDom`**, in answer shape.  Read-only, structural on `k`. -/
theorem binderDom_specA (k : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.binderDom k h
    ⦃fun r s' => s' = s₀ ∧
        denoteEO s₀.store r = (denoteE s₀.store h).map (Expr.binderDom k); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ h hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, binderDom_zero_eq] =>
      vcgen [ConRon.Arena.binderDom] <;> finish
  | succ k ih =>
    intro s₀ h hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, binderDom_succ_eq] =>
      vcgen [ConRon.Arena.binderDom, ih] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — **THEOREM 1
for `numArgs`**, in answer shape.  The arena's walk is fueled and FAILS at
fuel `0`; `; ⊤` claims nothing of a failure, so the equation is unconditional
on success. -/
theorem numArgs_specA (fuel : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.numArgs fuel h
    ⦃fun n s' => s' = s₀ ∧ (denoteE s₀.store h).map Expr.numArgs = some n; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro s₀ h _ _
    vcgen [ConRon.Arena.numArgs]
  | succ fuel ih =>
    intro s₀ h hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, numArgs_eq] =>
      vcgen [ConRon.Arena.numArgs, ih] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — **THEOREM 1
for `residualPW`**, in answer shape (the residual is `peelPisW`'s answer).
The level is read back with `readLevel`, which leaves the state alone. -/
theorem residualPW_specA (s₀ : AState) (r : Option EIdx)
    (hok : CheckOK mode env fe s₀) (hd : (denoteEO s₀.store r).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.residualPW r
    ⦃fun pw s' => s' = s₀ ∧ (denoteEO s₀.store r).map ConLeche.residualPW = some pw; ⊤⦄ := by
  obtain ⟨ox, hox⟩ := Option.isSome_iff_exists.mp hd
  sym only [bridge_grind, residualPW_some_eq, residualPW_none_eq] =>
    vcgen [ConRon.Arena.residualPW] <;> finish

/-! ## 3b. The identity-like wrappers (con-leche's task #342) -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-79 lamProj? — **THEOREM 1 for
`lamProj?`**.  Read-only; the arena's walk is fueled and fails at fuel `0`. -/
theorem lamProj?_specA (fuel : Nat) : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.lamProj? fuel k h
    ⦃fun r s' => s' = s₀ ∧ (denoteE s₀.store h).map (ConLeche.lamProj? k) = some r; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro k s₀ h _ _
    rw [ConRon.Arena.lamProj?]
    exact triple_fail
  | succ fuel ih =>
    intro k s₀ h hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, lamProj?_eq] =>
      vcgen [ConRon.Arena.lamProj?, ih] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:81-97 unwrapIdDefs — **THEOREM
1 for `unwrapIdDefs`**, in answer shape: the answer denotes con-leche's
unwrapping at the environment's lookup. -/
theorem unwrapIdDefs_specA (fuel : Nat) : ∀ (n : Nat) (s₀ : AState) (e : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store e).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.unwrapIdDefs fe fuel n e
    ⦃fun r s' => s' = s₀ ∧
        denoteE s₀.store r = (denoteE s₀.store e).map (ConLeche.unwrapIdDefs env.find? n); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ e _ hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, ConLeche.unwrapIdDefs] =>
      vcgen [ConRon.Arena.unwrapIdDefs] <;> finish
  | succ n ih =>
    intro s₀ e hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, unwrapIdDefs_succ_eq] =>
      vcgen [ConRon.Arena.unwrapIdDefs, ExprOps.getAppFn_spec fuel, viewConstName_spec,
        lamProj?_specA (mode := mode) (env := env) (fe := fe) fuel,
        ExprOps.getAppArgs_spec fuel, ih] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — **THEOREM 1
for `peelPisW`**, in answer shape. -/
theorem peelPisW_specA (fuel : Nat) : ∀ (k : Nat) (s₀ : AState) (e : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store e).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.peelPisW fe fuel k e
    ⦃fun r s' => s' = s₀ ∧
        denoteEO s₀.store r = (denoteE s₀.store e).map (ConLeche.peelPisW env.find? k); ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ e hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, peelPisW_zero_eq] =>
      vcgen [ConRon.Arena.peelPisW,
        unwrapIdDefs_specA (mode := mode) (env := env) (fe := fe) fuel] <;> finish
  | succ k ih =>
    intro s₀ e hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, peelPisW_succ_eq] =>
      vcgen [ConRon.Arena.peelPisW,
        unwrapIdDefs_specA (mode := mode) (env := env) (fe := fe) fuel, ih] <;> finish


/-! ## 4. The head readers -/

/-- con-leche: none — the twin's `substPWAt` with its nested-pattern cutoff
as a `Bool` test (`pwHasParams`), the shape `vcgen` gives `grind` a usable
fall-through for. -/
theorem substPWAt_split (lps : List NIdx) (us : LsIdx) (pw : PropWhen) :
    ConRon.Arena.substPWAt lps us pw =
      if pwHasParams pw then (do
        let ks ← readNamesM lps
        let vs ← readLevelsM us
        pure (some (Level.substPW ks vs pw)))
      else pure (some pw) := by
  cases pw with
  | never => rfl
  | ifAllZero ps => cases ps <;> rfl

/-- con-leche: ConLeche/Kernel/Level.lean substPW — **THEOREM 1 for
`substPWAt`**: `Level.substPW` at a stored constant's level parameters and a
use's universe arguments, with the cutoff hoisted over the readbacks. -/
theorem substPWAt_specX (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (pw : PropWhen) (ks : List ConLeche.Name) (vs : List Level)
    (hok : CheckOK mode env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.substPWAt lps us pw
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = some (Level.substPW ks vs pw); ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [substPWAt_split, readNamesM_specC (mode := mode) (env := env) (fe := fe),
      readLevelsM_specC (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:112-131 headTypePW — **THEOREM 1
for `headTypePW`** at the head's and the telescope root's denotations. -/
theorem headTypePW_specX (fuel : Nat) (s₀ : AState) (root : EIdx) (rx : Expr) (d : Nat)
    (h : EIdx) (x : Expr) (n : Nat) (hok : CheckOK mode env fe s₀)
    (hroot : denoteE s₀.store root = some rx) (hx : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headTypePW fe fuel root d h n
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.headTypePW env.find? rx d x n; ⊤⦄ := by
  sym only [bridge_grind, headTypePW_eq, residualPW_none_eq] =>
    vcgen [ConRon.Arena.headTypePW,
      peelPisW_specA (mode := mode) (env := env) (fe := fe) fuel,
      residualPW_specA (mode := mode) (env := env) (fe := fe),
      substPWAt_specX (mode := mode) (env := env) (fe := fe)
        (ks := (cValP (env.find? (exprConstName x))).levelParams) (vs := exprConstLevels x),
      binderDom_specA (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:136-140 typeSortPWGo — **THEOREM
1 for `typeSortPWGo`**, by induction on the fuel, at the type's and the root's
denotations. -/
theorem typeSortPWGo_specX (root : EIdx) (rx : Expr) (fuel : Nat) : ∀ (s₀ : AState)
    (R : EIdx) (x : Expr) (d : Nat), CheckOK mode env fe s₀ →
    denoteE s₀.store R = some x → denoteE s₀.store root = some rx →
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPWGo fe root fuel R d
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.typeSortPWGo env.find? rx x d; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro s₀ R x d _ _ _
    rw [ConRon.Arena.typeSortPWGo]
    exact triple_fail
  | succ fuel ih =>
    intro s₀ R x d hok hx hroot
    -- the induction hypothesis at the body's denotation
    have step := fun s₁ R₁ d₁ => ih s₁ R₁ (exprBody x) d₁
    clear ih
    sym only [bridge_grind, typeSortPWGo_eq] =>
      vcgen [ConRon.Arena.typeSortPWGo, ExprOps.getAppFn_spec fuel,
        numArgs_specA (mode := mode) (env := env) (fe := fe) fuel,
        headTypePW_specX (mode := mode) (env := env) (fe := fe) fuel (rx := rx)
          (x := x.getAppFn), step] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-150 typeSortPW — **THEOREM 1
for `typeSortPW`**, in answer shape. -/
theorem typeSortPW_specA (fuel : Nat) (s₀ : AState) (T : EIdx)
    (hok : CheckOK mode env fe s₀) (hT : (denoteE s₀.store T).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        (denoteE s₀.store T).map (ConLeche.typeSortPW env.find?) = some r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
  sym only [bridge_grind, ConLeche.typeSortPW] =>
    vcgen [ConRon.Arena.typeSortPW,
      typeSortPWGo_specX (mode := mode) (env := env) (fe := fe) T x fuel (x := x)] <;> finish

/-- con-leche: ConLeche/Kernel/FEnv.lean:256-260 FEnv.findProj? —
`findProjAt` with its answer as `ProjFound` (found together, and a found
entry's body denotes the environment's). -/
theorem projFoundAt {s : AState} {T : NIdx} {i : Nat} {Tn : ConLeche.Name}
    (hok : CheckOK mode env fe s) (hT : denoteN s.store.ns T = some Tn) :
    ProjFound s.store (fe.findProj? T i) (env.findProj? Tn i) := by
  obtain ⟨hsome, hnone⟩ := IFEnv.findProj?_spec T i Tn hok hT
  cases hr : fe.findProj? T i with
  | some en =>
    obtain ⟨p, hp1, hp2⟩ := hsome en hr
    rw [hp2]
    have h := entryAt s.store en
    rw [hp1] at h
    exact h
  | none => rw [hnone hr]; trivial

/-- con-leche: none — `ProjFound` at a handle's denotation, so that the lookup's
fact is keyed by the arena's lookup alone (`IndexAt`'s shape). -/
def ProjFoundAt (env : Env) (st : EStore) (r : Option IProjEntry) (i : Nat) :
    Option ConLeche.Name → Prop
  | some Tn => ProjFound st r (env.findProj? Tn i)
  | none => True

/-- con-leche: none — `projFoundAt` keyed by the invariant and the arena's
lookup. -/
theorem projFoundAt' {s : AState} (hok : CheckOK mode env fe s) (T : NIdx) (i : Nat) :
    ProjFoundAt env s.store (fe.findProj? T i) i (denoteN s.store.ns T) := by
  cases hT : denoteN s.store.ns T with
  | none => trivial
  | some Tn => exact projFoundAt hok hT
grind_pattern [bridge_grind] projFoundAt' => CheckOK mode env fe s, fe.findProj? T i

/-- con-leche: none — `ProjFoundAt` at a denoting handle. -/
theorem ProjFoundAt.some {st : EStore} {r : Option IProjEntry} {i : Nat}
    {Tn : ConLeche.Name} (H : ProjFoundAt env st r i (some Tn)) :
    ProjFound st r (env.findProj? Tn i) := H
grind_pattern [bridge_grind] ProjFoundAt.some => ProjFoundAt env st r i (some Tn)

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — **THEOREM 1
for `headProofPW`** at the head's denotation. -/
theorem headProofPW_specX (fuel : Nat) (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headProofPW fe fuel h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.headProofPW env.find? env.findTable? x; ⊤⦄ := by
  sym only [bridge_grind, headProofPW_eq] =>
    vcgen [ConRon.Arena.headProofPW,
      typeSortPW_specA (mode := mode) (env := env) (fe := fe) fuel,
      substPWAt_specX (mode := mode) (env := env) (fe := fe)
        (ks := (cValP (env.find? (exprConstName x))).levelParams) (vs := exprConstLevels x)] <;>
      finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — **THEOREM 1
for `proofPW`**, in answer shape: `annotPwLam` calls it on the knot's
`annotate` answer, and `notProofFast` / `isProofFast` on `propIrrel`'s
subjects. -/
theorem proofPW_specA (fuel : Nat) : ∀ (s₀ : AState) (a : EIdx),
    CheckOK mode env fe s₀ → (denoteE s₀.store a).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.proofPW fe fuel a
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        (denoteE s₀.store a).map (ConLeche.proofPW env.find? env.findTable?) = some r; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro s₀ a _ _
    rw [ConRon.Arena.proofPW]
    exact triple_fail
  | succ fuel ih =>
    intro s₀ a hok hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    sym only [bridge_grind, proofPW_eq] =>
      vcgen [ConRon.Arena.proofPW,
        headProofPW_specX (mode := mode) (env := env) (fe := fe) fuel (x := x), ih] <;> finish

/-! ## 5. The two arms

Both decide a GUARD of `propIrrel`, so each states BOTH Bool outcomes: the
answer is an equation with con-leche's `Bool`, which is the negative half as
much as the positive one. -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast — **THEOREM
1 for `notProofFast`**, in answer shape (`propIrrel` calls it on its two
subjects, which callers reach through `whnfCore` answers). -/
theorem notProofFast_specA (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀) (hd : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.notProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        (denoteE s₀.store a).map (ConLeche.notProofFast env.find? env.findTable?) = some b; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  sym only [bridge_grind, notProofFast_eq] =>
    vcgen [ConRon.Arena.notProofFast,
      proofPW_specA (mode := mode) (env := env) (fe := fe) fuel] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — **THEOREM
1 for `isProofFast`**, in answer shape. -/
theorem isProofFast_specA (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀) (hd : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        (denoteE s₀.store a).map (ConLeche.isProofFast env.find? env.findTable?) = some b; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  sym only [bridge_grind, isProofFast_eq] =>
    vcgen [ConRon.Arena.isProofFast,
      proofPW_specA (mode := mode) (env := env) (fe := fe) fuel] <;> finish

/-- con-leche: none — an answer through `Option.map` at a denoting subject. -/
theorem map_eq_some_at {α β : Type} {o : Option α} {f : α → β} {r : β} {x : α}
    (h : o.map f = some r) (ho : o = some x) : r = f x := by
  rw [ho] at h; exact (Option.some.inj h).symm

/-! ### `propIrrel`'s pure side at its five exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the "not a
proof" arm refuses, at any fuel. -/
theorem propIrrel_no {F d : Nat} {x y : Expr}
    (h : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = true) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, h, ite_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the "yes" arm
(the squash-regime licence), at any fuel. -/
theorem propIrrel_yes {F d : Nat} {x y : Expr}
    (hn : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = false)
    (h : (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) = true) :
    ConLeche.propIrrelFueled mode env F d x y = .ok true := by
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, h,
    Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path:
the first subject's type's type does not reduce to a sort. -/
theorem propIrrel_slow_a {F d : Nat} {x y ta tta w : Expr}
    (hn : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = false)
    (hi : (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok w := h3
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, ite_false, e1, e2, e3, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path:
the first subject's side is a sort, the second's type's type does not reduce
to one. -/
theorem propIrrel_slow_b {F d : Nat} {x y ta tta tb ttb w : Expr} {uT : Level}
    {okA : Bool}
    (hn : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = false)
    (hi : (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h4 : Level.isEquiv uT Level.zero = some okA)
    (h5 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h6 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h7 : ConLeche.whnf mode env F d ttb = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h3
  have e5 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h5
  have e6 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h6
  have e7 : (ConLeche.pureFns mode env F).whnf d ttb = .ok w := h7
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, ite_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
    h4, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path
to its end: both sides are sorts, and the verdict is the two level
comparisons' conjunction. -/
theorem propIrrel_slow {F d : Nat} {x y ta tta tb ttb : Expr} {uT vT : Level}
    {okA okB : Bool}
    (hn : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = false)
    (hi : (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h4 : Level.isEquiv uT Level.zero = some okA)
    (h5 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h6 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h7 : ConLeche.whnf mode env F d ttb = .ok (.sort vT))
    (h8 : Level.isEquiv vT Level.zero = some okB) :
    ConLeche.propIrrelFueled mode env F d x y = .ok (okA && okB) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h3
  have e5 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h5
  have e6 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h6
  have e7 : (ConLeche.pureFns mode env F).whnf d ttb = .ok (.sort vT) := h7
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, ite_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
    h4, h8, bind, Except.bind, pure, Except.pure]

/-! ### `propIrrel` -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.  The two fast arms are
`notProofFast_specA` / `isProofFast_specA` at both subjects — equations, so
both Bool outcomes of each guard transfer — and the slow path is
the `inferIO` slot twice and `KnotSpec.whnf'` once per side, the zero pin
and `lvlEq?_spec`, over a six-way fuel merge. -/
theorem propIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.propIrrel
  -- the two fast arms
  refine triple_seq (notProofFast_specA coreWalkFuel s₀ a hok (by rw [hda]; rfl)) ?_
  rintro na s1 ⟨hok1, hx1, hp1, hna⟩
  refine triple_seq (notProofFast_specA coreWalkFuel s1 b hok1
    (by rw [denote_ext hdb hx1]; rfl)) ?_
  rintro nb s2 ⟨hok2, hx2, hp2, hnb⟩
  have hx02 := hx1.trans hx2
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  have hN : (na || nb) = (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) := by
    rw [map_eq_some_at hna hda, map_eq_some_at hnb (denote_ext hdb hx1)]
  by_cases hNT : (na || nb) = true
  · rw [ite_eq_left hNT]
    exact triple_pureR ⟨hok2, hx02, hp02, 0, propIrrel_no (hN ▸ hNT)⟩
  rw [ite_eq_right hNT]
  have hNF : (ConLeche.notProofFast env.find? env.findTable? x ||
      ConLeche.notProofFast env.find? env.findTable? y) = false := by
    rw [← hN]; simpa using hNT
  refine triple_seq (isProofFast_specA coreWalkFuel s2 a hok2
    (by rw [denote_ext hda hx02]; rfl)) ?_
  rintro ia s3 ⟨hok3, hx3, hp3, hia⟩
  refine triple_seq (isProofFast_specA coreWalkFuel s3 b hok3
    (by rw [denote_ext hdb (hx02.trans hx3)]; rfl)) ?_
  rintro ib s4 ⟨hok4, hx4, hp4, hib⟩
  have hx04 := (hx02.trans hx3).trans hx4
  have hp04 : s4.pins = s₀.pins := hp4.trans (hp3.trans hp02)
  have hI : (ia && ib) = (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) := by
    rw [map_eq_some_at hia (denote_ext hda hx02),
      map_eq_some_at hib (denote_ext hdb (hx02.trans hx3))]
  by_cases hIT : (ia && ib) = true
  · rw [ite_eq_left hIT]
    exact triple_pureR ⟨hok4, hx04, hp04, 0, propIrrel_yes hNF (hI ▸ hIT)⟩
  rw [ite_eq_right hIT]
  have hIF : (ConLeche.isProofFast env.find? env.findTable? x &&
      ConLeche.isProofFast env.find? env.findTable? y) = false := by
    rw [← hI]; simpa using hIT
  -- the slow path: the first side's type's type
  refine triple_seq (hsim.inferIO s4 d a x hok4 (denote_ext hda hx04) hwa) ?_
  rintro ta s5 ⟨hok5, hx5, hp5, vta, hvta, hwvta, F1, hF1⟩
  refine triple_seq (hsim.inferIO s5 d ta vta hok5 hvta hwvta) ?_
  rintro tta s6 ⟨hok6, hx6, hp6, vtta, hvtta, hwvtta, F2, hF2⟩
  refine triple_seq (hsim.whnf s6 d tta vtta hok6 hvtta hwvtta) ?_
  rintro hh s7 ⟨hok7, hx7, hp7, vw, hvw, _, F3, hF3⟩
  have hx07 := ((hx04.trans hx5).trans hx6).trans hx7
  have hp07 : s7.pins = s₀.pins := hp7.trans (hp6.trans (hp5.trans hp04))
  obtain ⟨vv, hvv⟩ := denoteE_view hvw
  refine tag_view_bind_triple_else hvv ?_ (fun hne => ?_)
  rotate_left
  · -- not a sort
    have hns := denote_not_sort hok7.state.wf hvv hvw
      (fun u hh => hne (by rw [hh]; rfl))
    exact triple_pureR ⟨hok7, hx07, hp07, F1 + F2 + F3, propIrrel_slow_a hNF hIF
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hns⟩
  cases vv
  case sort uT =>
    obtain ⟨lT, rfl, hlT⟩ := denote_sort_inv hok7.state.wf hvv hvw
    dsimp only
    unfold ConRon.Arena.zeroLevel
    refine triple_seq (pinZeroLevel_spec s7 hok7.pins) ?_
    rintro z s8 ⟨hs8, hz⟩
    subst s8
    refine triple_seq (lvlEq?_spec s7 uT z hok7) ?_
    rintro q s9 ⟨hok9, hst9, hp9, lu, lv, hlu, hlv, hq⟩
    rw [hlT] at hlu; rw [hz] at hlv
    obtain rfl := Option.some.inj hlu
    obtain rfl := Option.some.inj hlv
    cases q with
    | none =>
      simp only [ConRon.Arena.liftFueled]
      exact triple_seq (Q := fun _ _ => False) triple_fail (fun _ _ h => h.elim)
    | some okA =>
      simp only [ConRon.Arena.liftFueled, pure_bind]
      have hx09 : Ext s₀.store s9.store := hx07.trans (by rw [hst9]; exact Ext.refl _)
      have hp09 : s9.pins = s₀.pins := hp9.trans hp07
      -- the second side
      refine triple_seq (hsim.inferIO s9 d b y hok9 (denote_ext hdb hx09) hwb) ?_
      rintro tb s10 ⟨hok10, hx10, hp10, vtb, hvtb, hwvtb, F4, hF4⟩
      refine triple_seq (hsim.inferIO s10 d tb vtb hok10 hvtb hwvtb) ?_
      rintro ttb s11 ⟨hok11, hx11, hp11, vttb, hvttb, hwvttb, F5, hF5⟩
      refine triple_seq (hsim.whnf s11 d ttb vttb hok11 hvttb hwvttb) ?_
      rintro hh2 s12 ⟨hok12, hx12, hp12, vw2, hvw2, _, F6, hF6⟩
      have hx012 := ((hx09.trans hx10).trans hx11).trans hx12
      have hp012 : s12.pins = s₀.pins := hp12.trans (hp11.trans (hp10.trans hp09))
      obtain ⟨vv2, hvv2⟩ := denoteE_view hvw2
      refine tag_view_bind_triple_else hvv2 ?_ (fun hne => ?_)
      rotate_left
      · have hns := denote_not_sort hok12.state.wf hvv2 hvw2
          (fun u hh => hne (by rw [hh]; rfl))
        exact triple_pureR ⟨hok12, hx012, hp012, F1 + F2 + F3 + F4 + F5 + F6,
          propIrrel_slow_b hNF hIF
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.inferTypeIO_mono (by omega) hF2)
            (ConLeche.whnf_mono (by omega) hF3) hq.symm
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.inferTypeIO_mono (by omega) hF5)
            (ConLeche.whnf_mono (by omega) hF6) hns⟩
      cases vv2
      case sort vT =>
        obtain ⟨lV, rfl, hlV⟩ := denote_sort_inv hok12.state.wf hvv2 hvw2
        dsimp only
        refine triple_seq (pinZeroLevel_spec s12 hok12.pins) ?_
        rintro z2 s13 ⟨hs13, hz2⟩
        subst s13
        refine triple_seq (lvlEq?_spec s12 vT z2 hok12) ?_
        rintro q2 s14 ⟨hok14, hst14, hp14, lu2, lv2, hlu2, hlv2, hq2⟩
        rw [hlV] at hlu2; rw [hz2] at hlv2
        obtain rfl := Option.some.inj hlu2
        obtain rfl := Option.some.inj hlv2
        cases q2 with
        | none =>
          exact triple_seq (Q := fun _ _ => False) triple_fail (fun _ _ h => h.elim)
        | some okB =>
          simp only [pure_bind]
          exact triple_pureR ⟨hok14,
            hx012.trans (by rw [hst14]; exact Ext.refl _), hp14.trans hp012,
            F1 + F2 + F3 + F4 + F5 + F6, propIrrel_slow hNF hIF
              (ConLeche.inferTypeIO_mono (by omega) hF1)
              (ConLeche.inferTypeIO_mono (by omega) hF2)
              (ConLeche.whnf_mono (by omega) hF3) hq.symm
              (ConLeche.inferTypeIO_mono (by omega) hF4)
              (ConLeche.inferTypeIO_mono (by omega) hF5)
              (ConLeche.whnf_mono (by omega) hF6) hq2.symm⟩
      all_goals
        dsimp only
        exact triple_pureR ⟨hok12, hx012, hp012, F1 + F2 + F3 + F4 + F5 + F6,
          propIrrel_slow_b hNF hIF
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.inferTypeIO_mono (by omega) hF2)
            (ConLeche.whnf_mono (by omega) hF3) hq.symm
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.inferTypeIO_mono (by omega) hF5)
            (ConLeche.whnf_mono (by omega) hF6)
            (denote_not_sort hok12.state.wf hvv2 hvw2 (fun _ h => nomatch h))⟩
  all_goals
    dsimp only
    exact triple_pureR ⟨hok7, hx07, hp07, F1 + F2 + F3, propIrrel_slow_a hNF hIF
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3)
      (denote_not_sort hok7.state.wf hvv hvw (fun _ h => nomatch h))⟩

/-! ## 6. The axiom census -/

section Census

#print axioms denote_not_sort
#print axioms denote_not_lam
#print axioms substPW_cutoff
/-! **The readers.** -/
#print axioms binderDom_specA
#print axioms numArgs_specA
#print axioms residualPW_specA
#print axioms lamProj?_specA
#print axioms unwrapIdDefs_specA
#print axioms peelPisW_specA
#print axioms substPWAt_specX
#print axioms headTypePW_specX
#print axioms typeSortPWGo_specX
#print axioms typeSortPW_specA
#print axioms headProofPW_specX
#print axioms proofPW_specA
#print axioms notProofFast_specA
#print axioms isProofFast_specA
/-! **The walk that waited on them.** -/
#print axioms propIrrel_slow
#print axioms propIrrel_spec

end Census

end ConRon.Bridge.Core

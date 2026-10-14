/-
# `ConRon.Bridge.Core.Walks.ProjLit` — the projection scrutinee's literal expansion

`projLitToCtor` is the `.proj` clause's second step: a string-literal
scrutinee expands to its constructor form (`Walks/StrCtor.lean`) and is
head-normalised before the projection table is consulted, when the stored
declarations support it (`strLitSupported`, `Walks/StrLit.lean`).

The proof is `sym only [bridge_grind] => vcgen […] <;> finish`: the answer
is a named predicate (`ProjLitAns`) with one `grind` lemma per exit
(`ProjLitAns.pass`, `ProjLitAns.whnf`), the twin's literal arm one
constructor deep (`projLitToCtor_split`).
-/
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.Core.Walks.PropRead

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## The projection table, as `grind` reads it

The projection table's entries as `grind` reads them: a lookup's answer as
ONE named predicate (`ProjAns`), a denoting entry's fields as equations
(`EntryFields`), a found entry as `some` of its projection (`projOf_eta`),
and the two callees in that shape (`findProj?_specP`,
`IProjEntry.fireOk_specA`). -/

/-- con-leche: none — the index's projection-table answer against the
environment's: a found entry denotes the environment's (which is found), a
miss is a miss. -/
def ProjAns (st : EStore) : Option IProjEntry → Option ProjEntry → Prop
  | some en, o => denoteProjEntry st en = o ∧ o.isSome = true
  | none, o => o = none

/-- con-leche: none — `ProjAns` at a found entry. -/
@[bridge_grind =] theorem ProjAns.some_eq (st : EStore) (en : IProjEntry) (o : Option ProjEntry) :
    ProjAns st (some en) o = (denoteProjEntry st en = o ∧ o.isSome = true) := rfl

/-- con-leche: none — `ProjAns` at a miss. -/
@[bridge_grind =] theorem ProjAns.none_eq (st : EStore) (o : Option ProjEntry) :
    ProjAns st none o = (o = none) := rfl

/-- con-leche: none — a found entry is `some` of its projection. -/
theorem projOf_eta {o : Option ProjEntry} (h : o.isSome = true) : o = some (projOf o) := by
  cases o with
  | none => cases h
  | some p => rfl
grind_pattern [bridge_grind] projOf_eta => o.isSome

/-- con-leche: none — a denoting entry's comparable fields: the constructor
and level-parameter handles denote the entry's, the counts are shared. -/
def EntryFields (st : EStore) (en : IProjEntry) : Option ProjEntry → Prop
  | some p => denoteN st.ns en.ctor = some p.ctor ∧
      Frontend.denoteNList st.ns en.levelParams = some p.levelParams ∧
      p.numParams = en.numParams ∧ p.numFields = en.numFields
  | none => True

/-- con-leche: none — `denoteProjEntry_inv`'s comparable fields, keyed by the
entry's denotation. -/
theorem entryFields (st : EStore) (en : IProjEntry) :
    EntryFields st en (denoteProjEntry st en) := by
  cases h : denoteProjEntry st en with
  | none => trivial
  | some p =>
    obtain ⟨_, hl, hc, _, _, _, _, hnp, hnf, _⟩ := denoteProjEntry_inv h
    exact ⟨hc, hl, hnp, hnf⟩
grind_pattern [bridge_grind] entryFields => denoteProjEntry st en

/-- con-leche: none — `EntryFields` at a denoting entry. -/
theorem EntryFields.some {st : EStore} {en : IProjEntry} {p : ProjEntry}
    (H : EntryFields st en (some p)) :
    denoteN st.ns en.ctor = some p.ctor ∧
      Frontend.denoteNList st.ns en.levelParams = some p.levelParams ∧
      p.numParams = en.numParams ∧ p.numFields = en.numFields := H
grind_pattern [bridge_grind] EntryFields.some => EntryFields st en (some p)

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? —
`IFEnv.findProj?_specA` with its answer as `ProjAns`. -/
theorem findProj?_specP (s₀ : AState) (T : NIdx) (i : Nat) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ fe.findProj? T i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ProjAns s'.store r (env.findProj? Tn i); ⊤⦄ :=
  triple_mono (IFEnv.findProj?_specA s₀ T i Tn hok hT)
    (fun r _ ⟨h1, h2, _, _, h5, h6⟩ => ⟨h1, h2, h5, by
      cases r with
      | none => exact (Option.some.inj h6).symm
      | some en =>
        simp only [denoteProjEntryO, Option.map_eq_some_iff] at h6
        obtain ⟨p, hp, hq⟩ := h6
        exact ⟨hp.trans hq, by rw [← hq]; rfl⟩⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:768-794 ProjEntry.fireOk —
`IProjEntry.fireOk_spec` at a denoting entry and level list, its answer over
their denotations (`projOf`, `Option.getD`): no record or list variable for
`grind` to bind. -/
theorem IProjEntry.fireOk_specA (s₀ : AState) (entry : IProjEntry) (us : LsIdx)
    (hok : CheckOK mode env fe s₀)
    (hden : (denoteProjEntry s₀.store entry).isSome = true)
    (hus : (denoteLs s₀.store.lss us).isSome = true) :
    ⦃fun s => s = s₀⦄ entry.fireOk us
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        b = (projOf (denoteProjEntry s₀.store entry)).fireOk
          ((denoteLs s₀.store.lss us).getD []); ⊤⦄ := by
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.mp hus
  rw [hls]
  exact IProjEntry.fireOk_spec s₀ entry us _ ls hok (projOf_eta hden) hls

/-- con-leche: none — a handle that denotes a literal views as that literal. -/
theorem view_of_denote_lit {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {l : Literal} (hv : st.view h = some v)
    (hd : denoteE st h = some (.lit l)) : v = .lit l := by
  cases v with
  | bvar i => have := denote_bvar_inv hwf hv hd; cases this
  | fvar k t => obtain ⟨_, h, _⟩ := denote_fvar_inv hwf hv hd; cases h
  | sort u => obtain ⟨_, h, _⟩ := denote_sort_inv hwf hv hd; cases h
  | const n us => obtain ⟨_, _, h, _, _⟩ := denote_const_inv hwf hv hd; cases h
  | app f a => obtain ⟨_, _, h, _, _⟩ := denote_app_inv hwf hv hd; cases h
  | lam ty b => obtain ⟨_, _, h, _, _⟩ := denote_lam_inv hwf hv hd; cases h
  | forallE ty b =>
    obtain ⟨_, _, h, _, _⟩ := denote_forallE_inv hwf hv hd; cases h
  | letE ty w b =>
    obtain ⟨_, _, _, h, _, _, _⟩ := denote_letE_inv hwf hv hd; cases h
  | lit l' => have := denote_lit_inv hwf hv hd; cases this; rfl
  | proj n i sub => obtain ⟨_, _, h, _, _⟩ := denote_proj_inv hwf hv hd; cases h

/-- con-leche: ConLeche/Kernel/Core.lean:680-685 projLitToCtor — does the
expansion fire: a string literal, and the stored declarations support it. -/
def projLitFires (env : Env) (x : Expr) : Bool :=
  exprTag x == ETag.lit && (litStr? (exprLit x)).isSome && ConLeche.strLitSupported env
attribute [bridge_grind =] projLitFires

/-- con-leche: ConLeche/Kernel/Core.lean:680-685 projLitToCtor — **the
answer** of the walk at the subject `x` (a named predicate: `SimEOp` at the
pure call, its `fun` hidden from `grind`). -/
def ProjLitAns (mode : CheckMode) (env : Env) (d : Nat) (x : Expr) (st : EStore)
    (r : EIdx) : Prop :=
  SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d st r

/-- con-leche: ConLeche/Kernel/Core.lean:680-685 projLitToCtor — the
pass-through exit: the subject is its own answer. -/
@[bridge_grind ←] theorem ProjLitAns.pass {d : Nat} {x : Expr} {st : EStore} {r : EIdx}
    (hd : denoteE st r = some x) (hw : Expr.WScoped d x)
    (hp : projLitFires env x = false) : ProjLitAns mode env d x st r := by
  refine ⟨x, hd, hw, 0, ?_⟩
  cases x with
  | lit l =>
    cases l with
    | natVal n => rfl
    | strVal str =>
      simp only [projLitFires, exprTag, exprLit, litStr?, ETag.lit, beq_self_eq_true,
        Option.isSome_some, Bool.true_and] at hp
      simp only [ConLeche.projLitToCtorFueled, ConLeche.projLitToCtor, hp,
        Bool.false_eq_true, ite_false]; rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:680-685 projLitToCtor — the
expansion exit: the `whnf` slot's answer at the constructor form. -/
theorem ProjLitAns.whnf {d : Nat} {x : Expr} {st : EStore} {r : EIdx} {str : String}
    (ht : exprTag x = ETag.lit) (hs : litStr? (exprLit x) = some str)
    (hsup : ConLeche.strLitSupported env = true)
    (hr : SimE (ConLeche.whnf mode env) d (ConLeche.strLitToConstructor str) st r) :
    ProjLitAns mode env d x st r := by
  obtain ⟨w, hw, hww, F, hF⟩ := hr
  refine ⟨w, hw, hww, F, ?_⟩
  rw [exprTag_lit ht]
  cases hl : exprLit x with
  | natVal n => rw [hl] at hs; cases hs
  | strVal s =>
    rw [hl] at hs; cases hs
    simp only [ConLeche.projLitToCtorFueled, ConLeche.projLitToCtor, hsup, ite_true]
    exact hF
grind_pattern [bridge_grind] ProjLitAns.whnf =>
  ProjLitAns mode env d x st r, SimE (ConLeche.whnf mode env) d (ConLeche.strLitToConstructor str) st r

grind_pattern [bridge_grind] strLitToConstructor_WScoped =>
  Expr.WScoped d (ConLeche.strLitToConstructor str)

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — the twin
with its literal arm one constructor deep (`litStr?` reads the literal), so
that `vcgen`'s fall-through conditions are flat
(`_tmp/corpus/vcgen-grind/nested-ctor-fallthrough-hyp.lean`). -/
theorem projLitToCtor_split (r : CoreFnsA) (d : Nat) (h : EIdx) :
    ConRon.Arena.projLitToCtor r fe d h =
    (if h.tag == ETag.lit then do
      match ← view h with
      | .lit l =>
        match litStr? l with
        | some s => do
          if ← ConRon.Arena.strLitSupported fe then do
            let c ← ConRon.Arena.strLitToConstructor s
            r.whnf d c
          else pure h
        | none => pure h
      | _ => pure h
    else pure h) := by
  simp only [ConRon.Arena.projLitToCtor]
  split
  · congr; funext v
    cases v with
    | lit l => cases l <;> rfl
    | _ => rfl
  · rfl

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — **THEOREM 1
for `projLitToCtor`**: a string-literal scrutinee expands to its reduced
constructor form before the projection table is consulted (answer
`ProjLitAns`, `SimEOp` at the pure call). -/
theorem projLitToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.projLitToCtor (coreKnot mode fe id fuel) fe d h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ProjLitAns mode env d x s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [projLitToCtor_split, strLitSupported_spec (mode := mode) (env := env) (fe := fe),
      strLitToConstructor_spec (mode := mode) (env := env) (fe := fe),
      KnotSpec.whnfS hsim] <;> finish

section Census

#print axioms projLitToCtor_spec

end Census

end ConRon.Bridge.Core

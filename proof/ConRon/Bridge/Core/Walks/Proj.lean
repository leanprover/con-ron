/-
# `ConRon.Bridge.Core.Walks.Proj` — the projection table, and the tier's one
structural gap closed

Task #97-P3-Core-2.  DESIGN §8's `### Task #97-P3-CoreWalks` §5 named exactly
one item of the Core-walks tier that was *not* labour:

> **The projection table has no denotation.**  `Arena/Frontend/Readback.lean`
> has `denoteCI` for an `IConstantInfo` and `denoteCV` for an `IConstantVal`,
> and nothing for an `IProjEntry` (`Arena/Env.lean:150`, ten fields, four of
> them handles).  So `IProjEntry.typeAt` **cannot be stated**, and neither can
> `projCert`, `IProjEntry.fireOk`, or the `.proj` arm of `whnfCoreBody` and
> `inferBody` below the guard. … **It should be the next round's first
> commit.**

`Bridge/Rel.lean`'s `denoteProjEntry` is that commit; this module is what it
unblocks.

## The four statements, and where each stands

| theorem | what it is | status |
|---|---|---|
| `projTableName_spec` | the reserved name of `T`'s table, interned | **CLOSED** |
| `IFEnv.findProj?_spec` | the indexed table lookup, at `denoteProjEntry` | **CLOSED**, modulo §2's shape hypothesis |
| `IProjEntry.fireOk_spec` | the tower-fire guard | **CLOSED** |
| `IProjEntry.typeAt_spec` | the `.proj` node's type | **CLOSED** (round 4) |
| `iotaCerts_spec` | the batched spine certificate | **CLOSED** (round 4) |
| `projCert_spec`, `projCertAt_spec` | the structural projection's certificate | **CLOSED** (round 4) |

## 1. The one thing the exactness lemma needs that neither tier records

`IProjTable.entry` (and con-leche's `ProjTable.entry`) read the two indexed
columns with a DEFAULT, and the two defaults are unrelated across the
denotation — `(default : EIdx)` need not denote `(default : Expr)` and
`(default : LIdx)` need not denote `Level.zero`.  So
`Bridge/Rel.lean`'s `denoteProjTable_entry` is exact exactly IN RANGE, and
`findProj?`'s own guard is `i < tbl.numFields`, which is in range only if the
two columns have `numFields` entries.

**That clause is ours, not con-leche's** (task #97-P3-Checker-2, correcting
this round's second finding).  It was booked here as a free hypothesis
`ProjTablesShaped` with a note that `Verify/EnvWF.lean:191`'s `ConstWF`
records the `bodies` half and not the `guards` half — but `ConstWF` is the
wrong place to take it from: **a simulation B ⇒ A takes invariants on the
REFINED side only**, `denoteProjTable` transports both columns pointwise and
copies `numFields` verbatim, so the pure table's sizes ARE ours.  The clause
is now `Bridge/StateOK.lean`'s `IProjTableOK`, a field of `IFEnvOK`, and
`findProj?_spec` reads it off `hok.ienv.proj` with no hypothesis of its own.
Its one debtor is the install (`Bridge/Checker/Inv.lean`'s
`projTableOK_of_install`, owned by the Inductives tier).

## 2. The `readNamesM` detour, and why it is here rather than at the spec

Task #97-P3-CoreWalks' **finding 3** — *"a registered `@[spec]` is a
commitment; state the frame in it the first time, because a caller cannot add
one later"* — bites a second time.  `Bridge/Specs.lean`'s three readback
specs were strengthened with the `caches` frame conjunct last round;
**`Bridge/SpecsL.lean`'s `readNamesM_spec` was not**, and `IProjEntry.fireOk`
reads a level-parameter list back.  Without the conjunct no caller can rebuild
`CacheOK`, and — measured last round, under `mvcgen` — the conjunct cannot
be supplied from the caller, by erasing the attribute or by passing a
stronger theorem.

The fix belongs at `SpecsL.lean`'s spec, and `SpecsL.lean` is **not this
round's lane** (`Bridge/ExprOps/**` is being closed concurrently against
`readNamesM` through `instLPFast_spec`, and strengthening a spec under a live
proof is how a merge breaks).  So this module first took the *first* shape
task #97-P3-CoreWalks §3 describes and then discarded: a body copy with no
spec of its own (`readNamesMB`, `= rfl` to `readNamesM`), a frame theorem
about the copy, and a `simp only` rewrite in front of the walk's `mvcgen`.
**Task #111 deleted the copy**: `vcgen` erases a registered spec per call, so
`readNamesM_frame` is stated about `readNamesM` itself, proved with
`vcgen [-readNamesM_spec, …]`, and `IProjEntry.fireOk_spec` erases the
spec the same way and passes the frame instead — the "erasing the
attribute" route `mvcgen` did not have.

**Ask for the coordinator** (still open): one conjunct in
`Bridge/SpecsL.lean`'s `readNamesM_spec`,
`s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧`, deletes §2
whole — the same one-line fix, at the same cost (`rfl`), as last round's.
-/
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.Spec
import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 0. Vocabulary candidates for Bridge/Grind.lean (task #123)

What this module's walks read and the generic vocabulary does not have yet:
the readback frame as `grind` composes it (reflexivity, transitivity, the
per-readback constructor keyed by the cache record as in
`Core/Walks/Cached.lean`'s `CheckOK.ofReadL`, its store/pins projections, and
`CheckOK` across it), the name-cache invariant off `CheckOK` (the sibling of
`CheckOK.readL'`), a handle LIST known only to denote, and the projection
table's optional entry as a denotation (`denoteProjEntryO`, `denoteEO`'s
shape). -/

grind_pattern [bridge_grind] ReadbackFrame.refl => ReadbackFrame s s
grind_pattern [bridge_grind] ReadbackFrame.trans => ReadbackFrame s₀ s₁, ReadbackFrame s₁ s₂
grind_pattern [bridge_grind] ReadbackFrame.ofReadN =>
  ({ s0.caches with readNC := s1.caches.readNC } : Caches)
attribute [bridge_grind →] ReadbackFrame.store ReadbackFrame.pins
grind_pattern [bridge_grind] CheckOK.ofReadbackFrame => CheckOK mode env fe s, ReadbackFrame s s'

/-- con-leche: none — the name-readback table's invariant off `CheckOK` (as
`CheckOK.readL'`). -/
theorem CheckOK.readN' {s : AState} (h : CheckOK mode env fe s) :
    ReadNCacheOK s.caches.readNC s.store := h.caches.readN

/-- con-leche: none — a handle list known only to denote denotes a named list
(`ExprOps.isSome_eq_some` at lists). -/
theorem isSome_eq_someL {o : Option (List Expr)} (h : o.isSome = true) :
    o = some (o.getD []) := by
  cases o <;> simp_all
grind_pattern [bridge_grind] isSome_eq_someL => o.isSome

/-- con-leche: none — the denotation of an OPTIONAL projection entry, so that
a lookup's answer is one equation (`denoteEO`'s shape). -/
def denoteProjEntryO (st : EStore) : Option IProjEntry → Option (Option ProjEntry)
  | none => some none
  | some e => (denoteProjEntry st e).map some

/-! ## 1. The reserved table name -/

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName — **THEOREM 1
for `projTableName`**: the handle the twin interns denotes con-leche's
reserved name `(T.str "projTable").num 0`.  Two `internNNode`s, in
`Bridge/Specs.lean`'s `internName_spec` shape. -/
theorem projTableName_spec (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (hwf : StoreWF s₀.store) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projTableName T
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projTableName Tn); ⊤⦄ := by
  sym only [bridge_grind, denoteNView, Arena.NStore.ViewOK, NNodeView.children,
      List.mem_singleton, nview_isSome_of_denote, ConLeche.projTableName] =>
    vcgen [ConRon.Arena.projTableName, internNNode_spec] <;> finish

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName —
`projTableName_spec` at the tier's invariant (`CheckOK.mono`), for the lookup
below. -/
theorem projTableName_specC (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projTableName T
    ⦃fun h s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projTableName Tn); ⊤⦄ :=
  triple_mono (projTableName_spec s₀ T Tn hok.state.wf hT)
    (fun _ _ ⟨hwf, hx, hm, hc, hp, hd⟩ => ⟨hok.mono ⟨hwf⟩ hx hc hp, hx, hm, hc, hp, hd⟩)

/-! ## 2. The shape clause con-leche's `ConstWF` half-records -/

/-! ## 3. The lookup -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — the index
stores a TABLE at the reserved name: the entry the arena answers with denotes
con-leche's (`IFEnvOK.hit` at the reserved name, `denoteCI`'s `.projInfo` arm
and `denoteProjTable_entry`).  Task #120: the hit arm as a lemma; since task
#123 `findProjAt` reads all three as one equation. -/
theorem findProj?_hit_some {s : AState} {rn : NIdx} {tbl : IProjTable}
    {Tn : ConLeche.Name} {i : Nat} (hck : CheckOK mode env fe s)
    (hfind : fe.find? rn = some (.projInfo tbl))
    (hdn : denoteN s.store.ns rn = some (ConLeche.projTableName Tn)) :
    ∀ e, (if i < tbl.numFields then some (tbl.entry i) else none) = some e →
      ∃ p, denoteProjEntry s.store e = some p ∧ env.findProj? Tn i = some p := by
  obtain ⟨nm, ci, hnm, hci, hfindE⟩ := hck.ienv.hit rn _ hfind
  obtain rfl : nm = ConLeche.projTableName Tn := by
    rw [hnm] at hdn; exact Option.some.inj hdn
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
  obtain ⟨pt, hpt, rfl⟩ := hci
  obtain ⟨hnf, _, _⟩ := denoteProjTable_fields hpt
  obtain ⟨hbsz, hgsz, -⟩ := hck.ienv.proj rn tbl hfind
  intro e he
  split at he
  next hlt =>
    obtain rfl := Option.some.inj he
    exact ⟨pt.entry i,
      denoteProjTable_entry hpt (by rw [hbsz]; exact hlt) (by rw [hgsz]; exact hlt),
      ConLeche.Env.findProj?_of_table hfindE (by rw [hnf]; exact hlt)⟩
  next => exact absurd he (by simp)

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — the table's
slot is out of range in both tiers (the two `numFields` are one number). -/
theorem findProj?_hit_none {s : AState} {rn : NIdx} {tbl : IProjTable}
    {Tn : ConLeche.Name} {i : Nat} (hck : CheckOK mode env fe s)
    (hfind : fe.find? rn = some (.projInfo tbl))
    (hdn : denoteN s.store.ns rn = some (ConLeche.projTableName Tn)) :
    (if i < tbl.numFields then some (tbl.entry i) else none) = none →
      env.findProj? Tn i = none := by
  obtain ⟨nm, ci, hnm, hci, hfindE⟩ := hck.ienv.hit rn _ hfind
  obtain rfl : nm = ConLeche.projTableName Tn := by
    rw [hnm] at hdn; exact Option.some.inj hdn
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
  obtain ⟨pt, hpt, rfl⟩ := hci
  obtain ⟨hnf, _, _⟩ := denoteProjTable_fields hpt
  intro he
  split at he
  next => exact absurd he (by simp)
  next hlt =>
    simp only [ConLeche.Env.findProj?, hfindE]
    exact ite_eq_right (by rw [hnf]; exact hlt)

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — the index
stores no table at the reserved name, so neither does the environment
(`IFEnvOK.miss` through `denoteN_inj`, or a non-table entry). -/
theorem findProj?_miss_none {s : AState} {rn : NIdx} {Tn : ConLeche.Name}
    {i : Nat} (hck : CheckOK mode env fe s)
    (hno : ∀ tbl, fe.find? rn ≠ some (.projInfo tbl))
    (hdn : denoteN s.store.ns rn = some (ConLeche.projTableName Tn)) :
    (none : Option IProjEntry) = none → env.findProj? Tn i = none := by
  intro _
  cases hf : fe.find? rn with
  | none =>
    exact ConLeche.Env.findProj?_none_of_fresh
      (IFEnvOK.miss hck.state hck.ienv hdn hf) i
  | some ci =>
    obtain ⟨nm, c, hnm, hci, hfindE⟩ := hck.ienv.hit rn ci hf
    obtain rfl : nm = ConLeche.projTableName Tn := by
      rw [hnm] at hdn; exact Option.some.inj hdn
    simp only [ConLeche.Env.findProj?, hfindE]
    cases c
    case projInfo pt =>
      obtain ⟨tbl, rfl, _⟩ := denoteCI_projInfo hci
      exact (hno tbl hf).elim
    all_goals rfl

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — the arena's
lookup at the reserved name's handle, as a pure function (the program's
`match`, so that `grind` reads both arms off one term). -/
def iFindProj (fe : IFEnv) (rn : NIdx) (i : Nat) : Option IProjEntry :=
  match fe.find? rn with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — **the lookup
as ONE equation** (task #123): at a handle denoting `T`'s reserved name, the
arena's answer denotes con-leche's — the three lemmas above, keyed by the
invariant, the name's denotation and the comparand. -/
theorem findProjAt {s : AState} {rn : NIdx} {Tn : ConLeche.Name} {i : Nat}
    (hck : CheckOK mode env fe s)
    (hdn : denoteN s.store.ns rn = some (ConLeche.projTableName Tn)) :
    denoteProjEntryO s.store (iFindProj fe rn i) = some (env.findProj? Tn i) := by
  unfold iFindProj
  split
  · rename_i tbl hfind
    cases hif : (if i < tbl.numFields then some (tbl.entry i) else none) with
    | none =>
      rw [findProj?_hit_none hck hfind hdn hif]; rfl
    | some e =>
      obtain ⟨p, hp, hfp⟩ := findProj?_hit_some hck hfind hdn e hif
      rw [hfp]; simp [denoteProjEntryO, hp]
  · rename_i hno
    rw [findProj?_miss_none hck (fun tbl h => hno tbl h) hdn rfl]; rfl
grind_pattern [bridge_grind] findProjAt =>
  CheckOK mode env fe s, denoteN s.store.ns rn, env.findProj? Tn i where
  guard denoteN s.store.ns rn = some (ConLeche.projTableName Tn)

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — Theorem 1 for
the lookup with its answer as one equation (task #123: no `∃` for `grind` to
prove). -/
theorem IFEnv.findProj?_specA (s₀ : AState) (T : NIdx) (i : Nat)
    (Tn : ConLeche.Name) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ fe.findProj? T i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteProjEntryO s'.store r = some (env.findProj? Tn i); ⊤⦄ := by
  sym only [bridge_grind, iFindProj, denoteProjEntryO] =>
    vcgen [ConRon.Arena.IFEnv.findProj?,
      projTableName_specC (Tn := Tn) (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — **THEOREM 1
for the indexed projection-table lookup**: the entry the arena answers with
denotes the entry con-leche's environment answers with, and a miss is a miss.

The `some` half is `IFEnvOK.hit` at the reserved name, `denoteCI`'s
`.projInfo` arm, and `Bridge/Rel.lean`'s `denoteProjTable_entry`; the `none`
half is `IFEnvOK.miss` (through `denoteN_inj`) and the fact that the two
`numFields` are literally the same number. -/
theorem IFEnv.findProj?_spec (s₀ : AState) (T : NIdx) (i : Nat)
    (Tn : ConLeche.Name) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ fe.findProj? T i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ e, r = some e → ∃ p, denoteProjEntry s'.store e = some p ∧
          env.findProj? Tn i = some p) ∧
        (r = none → env.findProj? Tn i = none); ⊤⦄ := by
  refine triple_mono (IFEnv.findProj?_specA s₀ T i Tn hok hT) ?_
  rintro r s' ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, h4, h5, fun e he => ?_, fun he => ?_⟩
  · subst he
    simp only [denoteProjEntryO, Option.map_eq_some_iff] at h6
    obtain ⟨p, hp, hpe⟩ := h6
    exact ⟨p, hp, hpe.symm⟩
  · subst he
    exact (Option.some.inj h6).symm

/-! ## 4. `IProjEntry.fireOk` — CLOSED

The module note's §2 detour, then the walk. -/

/-- con-leche: none — **the frame of a `readNamesM` call**, which
`Bridge/SpecsL.lean`'s registered spec does not carry.  One list induction
over `readNameM_spec`, whose own frame conjunct `Bridge/Specs.lean` has; the
registered `readNamesM_spec` is erased for the two calls (`vcgen [-…]`, see
the module note §2). -/
theorem readNamesM_frame (s₀ : AState) (hs : List NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.readNamesM hs
    ⦃fun xs s' => ReadbackFrame s₀ s' ∧
        Frontend.denoteNList s₀.store.ns hs = some xs; ⊤⦄ := by
  induction hs generalizing s₀ with
  | nil =>
    sym only [bridge_grind, Frontend.denoteNList] =>
      vcgen [-readNamesM_spec, ConRon.Arena.readNamesM] <;> finish
  | cons a as ih =>
    sym only [bridge_grind, Frontend.denoteNList] =>
      vcgen [-readNamesM_spec, ConRon.Arena.readNamesM, readNameM_spec, ih] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:768-794 ProjEntry.fireOk —
**THEOREM 1 for the tower-fire guard**: at a `Prop`-declared structure the
field's guard level must be a proposition at this instantiation; at every
other family the rule fires unconditionally.

CLOSED.  `lvlEq?_spec` (`Bridge/Core/Walks/Cached.lean`, closed) decides the
structure sort against the zero pin, the three readbacks give the level
parameters, the instantiation levels and the field sort, and the rest is
`Level.subst`/`Level.isEquiv` on values both tiers share — no `ExprOps` rule,
no fuel, no `∃ F`. -/
theorem IProjEntry.fireOk_spec (s₀ : AState) (entry : IProjEntry) (us : LsIdx)
    (p : ProjEntry) (ls : List Level) (hok : CheckOK mode env fe s₀)
    (hden : denoteProjEntry s₀.store entry = some p)
    (hus : denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => s = s₀⦄ entry.fireOk us
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = p.fireOk ls; ⊤⦄ := by
  obtain ⟨_hs, hlps, _hc, _hb, hfs, hss, _hi, _hnp, _hnf, _ho⟩ :=
    denoteProjEntry_inv hden
  simp only [ConRon.Arena.IProjEntry.fireOk, ConRon.Arena.zeroLevel]
  sym only [bridge_grind, ConLeche.ProjEntry.fireOk, → CheckOK.readL', → CheckOK.readLs',
      → CheckOK.readN', hok.pins] =>
    vcgen [lvlEq?_spec (mode := mode) (env := env) (fe := fe), -readNamesM_spec,
      readNamesM_frame] <;> finish

/-! ## 5. The two that waited on another tier — CLOSED (round 4) -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
`ExprOps/Subst.lean`'s `instantiateListFast_spec` at the tier's invariant
(`CheckOK.mono`; task #123, as `Core/Walks/Spine.lean`'s `mkAppN_specC`). -/
theorem instantiateListFast_specC (fuel : Nat) (s₀ : AState) (e : EIdx)
    (vs : Array EIdx) (d : Nat) (ws : List Expr) (hok : CheckOK mode env fe s₀)
    (hvec : ExprOps.InstLVec s₀.store vs ws)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiateListFast fuel e vs d
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        ExprOps.InstLAt ws d s₀.store e s'.store r; ⊤⦄ :=
  triple_mono (ExprOps.instantiateListFast_spec fuel s₀ e vs d ws hok.state hvec hden)
    (fun _ _ ⟨hst, hx, hc, hp, _, hrel⟩ => ⟨hok.mono hst hx hc hp, hx, hp, hrel⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt —
**THEOREM 1 for the type of a `.proj` node at a tower-backed entry**: the
stored body, level-instantiated at the subject type's levels, with the
subject type's arguments and the subject substituted for its `numParams + 1`
loose variables in ONE traversal.

**CLOSED** (round 4): `instLPFast_spec` (with its cache frame) then
`instantiateListFast_spec` on the push-order array `targs.toArray.push pe`
(task #97-P6-15's accumulator ruling), whose `InstLVec` is exactly
`pe :: targs.reverse`. -/
theorem IProjEntry.typeAt_spec (s₀ : AState) (entry : IProjEntry) (us : LsIdx)
    (targs : List EIdx) (pe : EIdx) (p : ProjEntry) (ls : List Level)
    (xs : List Expr) (x : Expr) (hok : CheckOK mode env fe s₀)
    (hden : denoteProjEntry s₀.store entry = some p)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store targs = some xs)
    (hpe : denoteE s₀.store pe = some x) :
    ⦃fun s => s = s₀⦄ entry.typeAt us targs pe
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (p.typeAt ls xs x); ⊤⦄ := by
  obtain ⟨_hs, hlps, _hc, hb, _hfs, _hss, _hi, _hnp, _hnf, _ho⟩ :=
    denoteProjEntry_inv hden
  have hvec : ExprOps.InstLVec s₀.store (targs.toArray.push pe)
      (x :: xs.reverse) := by
    unfold ExprOps.InstLVec
    simp only [Array.toList_push, List.reverse_cons,
      List.reverse_reverse]
    exact ExprOps.denoteEList_snoc hpe _ _ hargs
  -- the push-order vector denotes `pe :: targs.reverse` (task #97-P6-15);
  -- `RelE_eq_ans` (Cached's `Ans` reading of `RelE`) is off: `ExprOps/Subst.lean`'s
  -- `RelE_eq_mapRel` reads the same answers without a `fun`
  sym only [bridge_grind, -RelE_eq_ans, ConLeche.ProjEntry.typeAt] =>
    vcgen [ConRon.Arena.IProjEntry.typeAt,
      ExprOps.instLPFast_spec coreWalkFuel s₀ entry.levelParams us entry.body _ _ hok.state
        hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus (by rw [hb]; rfl),
      fun (s : AState) (e : EIdx) => instantiateListFast_specC (mode := mode) (env := env)
        (fe := fe) coreWalkFuel s e (targs.toArray.push pe) 0 (x :: xs.reverse)] <;> finish

/-! ## 5a. `iotaCertsFull` — the batched full-grade telescope certificate

`Arena/Core.lean`'s `iotaCertsFullAux` carries a PUSH-order accumulator of
pending substitutions (task #97-P6-9) and matches on the UN-instantiated
telescope, flushing at a `.bvar` head; con-leche's `iotaCertsFull` (task
#342 L10: ι's case 3, every slot at the FULL grade) substitutes eagerly.  The
two meet through `ExprOps/Subst.lean`'s `InstLVec`: at every step the arena's
`(h, acc)` denotes con-leche's `tyx.instantiateList ws`.  This is con-leche's
own cached-tier simulation, and the induction is its lexicographic measure
`(args.size - i, acc.size)`. -/

/-- con-leche: ConLeche/Kernel/Core.lean:251-259 iotaCertsFull — the spine
ran out: certified. -/
theorem iotaCertsFullFueled_nil {F d : Nat} {ty : Expr} :
    ConLeche.iotaCertsFullFueled mode env F d ty [] = .ok true := by
  simp only [ConLeche.iotaCertsFullFueled, ConLeche.iotaCertsFull]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:251-259 iotaCertsFull — a certified
slot: the argument's FULL-grade type agrees with the domain, and the walk
continues. -/
theorem iotaCertsFullFueled_cert {F d : Nat} {t b : Expr} {x ta : Expr}
    {xs : List Expr}
    (h1 : ConLeche.inferTypeCore mode env F d x = .ok ta)
    (h2 : ConLeche.isDefEqCore mode env F d ta t = .ok true) :
    ConLeche.iotaCertsFullFueled mode env F d (.forallE t b) (x :: xs) =
      ConLeche.iotaCertsFullFueled mode env F d (b.instantiate1 x) xs := by
  have e1 : (ConLeche.pureFns mode env F).infer d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).defeq d ta t = .ok true := h2
  simp only [ConLeche.iotaCertsFullFueled, ConLeche.iotaCertsFull, e1, e2,
    bind, Except.bind, ite_true]

/-- con-leche: ConLeche/Kernel/Core.lean:251-259 iotaCertsFull — a slot
whose argument's type does not agree: declined. -/
theorem iotaCertsFullFueled_fail {F d : Nat} {t b : Expr} {x ta : Expr}
    {xs : List Expr}
    (h1 : ConLeche.inferTypeCore mode env F d x = .ok ta)
    (h2 : ConLeche.isDefEqCore mode env F d ta t = .ok false) :
    ConLeche.iotaCertsFullFueled mode env F d (.forallE t b) (x :: xs) =
      .ok false := by
  have e1 : (ConLeche.pureFns mode env F).infer d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).defeq d ta t = .ok false := h2
  simp only [ConLeche.iotaCertsFullFueled, ConLeche.iotaCertsFull, e1, e2,
    bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:251-259 iotaCertsFull — arguments
left over and no binder to take them: declined. -/
theorem iotaCertsFullFueled_notpi {F d : Nat} {ty x : Expr}
    {xs : List Expr} (h : ∀ t b, ty ≠ .forallE t b) :
    ConLeche.iotaCertsFullFueled mode env F d ty (x :: xs) = .ok false := by
  cases ty <;> simp_all [ConLeche.iotaCertsFullFueled, ConLeche.iotaCertsFull] <;> rfl

/-- con-leche: none — a denoting suffix of an argument array, peeled at its
first index. -/
theorem denoteEList_drop_cons {st : EStore} {args : Array EIdx} {i : Nat}
    {xs : List Expr} (hi : i < args.size)
    (h : Frontend.denoteEList st (args.toList.drop i) = some xs) :
    ∃ x xs', xs = x :: xs' ∧ denoteE st args[i] = some x ∧
      Frontend.denoteEList st (args.toList.drop (i + 1)) = some xs' := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)] at h
  obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv h
  exact ⟨x, xs', rfl, by simpa using hx, hxs⟩

/-- con-leche: none — the push-order accumulator, extended by one. -/
theorem InstLVec.push {st : EStore} {acc : Array EIdx} {ws : List Expr}
    {a : EIdx} {x : Expr} (h : ExprOps.InstLVec st acc ws)
    (hx : denoteE st a = some x) : ExprOps.InstLVec st (acc.push a) (x :: ws) := by
  unfold ExprOps.InstLVec at h ⊢
  simp only [Array.toList_push, List.reverse_cons]
  exact ExprOps.denoteEList_snoc hx _ _ h

/-- con-leche: none — the accumulator's denotation is functional. -/
theorem InstLVec.unique {st : EStore} {acc : Array EIdx} {ws ws' : List Expr}
    (h : ExprOps.InstLVec st acc ws) (h' : ExprOps.InstLVec st acc ws') :
    ws = ws' := by
  unfold ExprOps.InstLVec at h h'
  exact List.reverse_inj.mp (Option.some.inj (h.symm.trans h'))

/-- con-leche: none — the empty accumulator denotes the empty list. -/
theorem InstLVec.empty (st : EStore) : ExprOps.InstLVec st #[] [] := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211 instantiateList — at a ∀. -/
theorem instantiateList_forallE {t b : Expr}
    {ws : List Expr} :
    (Expr.forallE t b).instantiateList ws =
      .forallE (t.instantiateList ws) (b.instantiateList ws 1) := by
  simp [Expr.instantiateList]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211 instantiateList — a head
that is neither a ∀ nor a loose variable keeps its constructor, so it is not
a ∀ afterwards either. -/
theorem instantiateList_not_forallE {e : Expr} {ws : List Expr}
    (hf : ∀ t b, e ≠ .forallE t b) (hb : ∀ k, e ≠ .bvar k) :
    ∀ t b, e.instantiateList ws ≠ .forallE t b := by
  cases e <;> simp_all [Expr.instantiateList]

/-- con-leche: none — a handle whose VIEW is neither a ∀ nor a loose
variable denotes neither. -/
theorem denote_not_forallE_bvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b, v = .forallE ty b → False)
    (hnb : ∀ k, v = .bvar k → False) :
    (∀ p q, e ≠ .forallE p q) ∧ ∀ k, e ≠ .bvar k := by
  cases v with
  | bvar i => exact absurd rfl (hnb i)
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨p, q, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b => exact absurd rfl (hne ty b)
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean iotaCertsFullCAux_sim —
**the induction**, in ∃/∀ shape (the recursive calls' subjects are answers
of `instantiateListFast` and of the accumulator push). -/
theorem iotaCertsFullAux_go {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args : Array EIdx) :
    ∀ (k m : Nat) (h : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState),
      args.size - i = k → acc.size = m → CheckOK mode env fe s₀ →
      (∃ tyx ws xs, denoteE s₀.store h = some tyx ∧
        ExprOps.InstLVec s₀.store acc ws ∧
        Expr.WScoped d (tyx.instantiateList ws) ∧
        Frontend.denoteEList s₀.store (args.toList.drop i) = some xs ∧
        ∀ x ∈ xs, Expr.WScoped d x) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.iotaCertsFullAux (coreKnot mode fe id fuel) fe d h acc
          args i
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∀ tyx ws xs, denoteE s₀.store h = some tyx →
            ExprOps.InstLVec s₀.store acc ws →
            Frontend.denoteEList s₀.store (args.toList.drop i) = some xs →
            SimBOp (fun F => ConLeche.iotaCertsFullFueled mode env F d
              (tyx.instantiateList ws) xs) r; ⊤⦄ := by
  have tpure : ∀ {s : AState} {v : Bool} {Q : Bool → AState → Prop}, Q v s →
      ⦃fun s' => s' = s⦄ (pure v : AM Bool) ⦃fun r s' => Q r s'; ⊤⦄ := by
    intro s v Q h
    vcgen
    subst_vars; exact h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro h acc i s₀ hk hm hok hpre
  obtain ⟨tyx, ws, xs, hh, hacc, hwty, hxs, hwxs⟩ := hpre
  have hwf := hok.state.wf
  -- the postcondition's three subjects are functional
  suffices key : ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaCertsFullAux (coreKnot mode fe id fuel) fe d h acc args i
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.iotaCertsFullFueled mode env F d
          (tyx.instantiateList ws) xs) r; ⊤⦄ by
    refine triple_mono key ?_
    rintro r s' ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun tyx' ws' xs' e1 e2 e3 => ?_⟩
    obtain rfl := Option.some.inj (e1.symm.trans hh)
    obtain rfl := InstLVec.unique e2 hacc
    obtain rfl := Option.some.inj (e3.symm.trans hxs)
    exact h4
  rw [ConRon.Arena.iotaCertsFullAux]
  by_cases hi : i < args.size
  · rw [dite_eq_left hi]
    obtain ⟨x, xs', rfl, hx, hxs'⟩ := denoteEList_drop_cons hi hxs
    have hwx : Expr.WScoped d x := hwxs x (by simp)
    have hwxs' : ∀ z ∈ xs', Expr.WScoped d z :=
      fun z hz => hwxs z (by simp [hz])
    obtain ⟨v, hv⟩ := denoteE_view hh
    refine view_bind_triple hv ?_
    cases v
    case forallE ty b =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denote_forallE_inv hwf hv hh
      rw [instantiateList_forallE]
      simp only [instantiateList_forallE, Expr.WScoped] at hwty
      dsimp only
      refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty
        acc 0 ws hok.state hacc (by rw [hp]; rfl)) ?_
      rintro ty2 s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
      have hok1 := hok.mono hst1 hx1 hc1 hp1
      have hty2 : denoteE s1.store ty2 = some (p.instantiateList ws) :=
        hrel1 _ hp
      refine triple_seq (hsim.infer s1 d args[i] x hok1 (denote_ext hx hx1)
        hwx) ?_
      rintro ta s2 ⟨hok2, hx2, hp2, vta, hvta, hwvta, F1, hF1⟩
      refine triple_seq (hsim.defeq s2 d ta ty2 vta _ hok2 hvta
        (denote_ext hty2 hx2) hwvta hwty.1) ?_
      rintro bb s3 ⟨hok3, hx3, hp3, F2, hF2⟩
      have hx03 : Ext s₀.store s3.store := hx1.trans (hx2.trans hx3)
      cases bb
      · simp only [Bool.false_eq_true, ite_false]
        exact tpure ⟨hok3, hx03, by rw [hp3, hp2, hp1], F1 + F2,
          iotaCertsFullFueled_fail (ConLeche.inferTypeCore_mono (by omega) hF1)
            (ConLeche.isDefEqCore_mono (by omega) hF2)⟩
      · simp only [ite_true]
        have hwq : Expr.WScoped d (q.instantiateList (x :: ws)) := by
          rw [Expr.instantiateList_cons]
          exact Expr.WScoped.instantiate1_gen hwx 0 hwty.2
        refine triple_mono (ihk (args.size - (i + 1)) (by omega)
          (acc.push args[i]).size b (acc.push args[i]) (i + 1) s3 rfl rfl hok3
          ⟨q, x :: ws, xs', denote_ext hq hx03,
            InstLVec.push (hacc.ext hx03) (denote_ext hx hx03), hwq,
            denoteEList_ext hx03 _ _ hxs', hwxs'⟩) ?_
        rintro r s4 ⟨hok4, hx4, hp4, hr⟩
        obtain ⟨F3, hF3⟩ := hr q (x :: ws) xs' (denote_ext hq hx03)
          (InstLVec.push (hacc.ext hx03) (denote_ext hx hx03))
          (denoteEList_ext hx03 _ _ hxs')
        refine ⟨hok4, hx03.trans hx4, by rw [hp4, hp3, hp2, hp1],
          F1 + F2 + F3, ?_⟩
        show ConLeche.iotaCertsFullFueled mode env _ d _ _ = _
        rw [iotaCertsFullFueled_cert (ConLeche.inferTypeCore_mono (by omega) hF1)
          (ConLeche.isDefEqCore_mono (by omega) hF2),
          ← Expr.instantiateList_cons]
        exact iotaCertsFullFueled_mono (by omega) hF3
    case bvar k0 =>
      dsimp only
      by_cases hz : acc.size = 0
      · rw [ite_eq_left hz]
        have hws : ws = [] := by
          have h0 : acc = #[] := Array.eq_empty_of_size_eq_zero hz
          subst h0
          exact InstLVec.unique hacc (InstLVec.empty _)
        subst hws
        refine tpure ⟨hok, Ext.refl _, rfl, 0, ?_⟩
        rw [denote_bvar_inv hwf hv hh, ConLeche.Expr.instantiateList_nil]
        exact iotaCertsFullFueled_notpi (by simp)
      · rw [ite_eq_right hz]
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ h
          acc 0 ws hok.state hacc (by rw [hh]; rfl)) ?_
        rintro ty2 s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
        have hok1 := hok.mono hst1 hx1 hc1 hp1
        have hty2 : denoteE s1.store ty2 = some (tyx.instantiateList ws) :=
          hrel1 _ hh
        refine triple_mono (ihm 0 (by omega) ty2 #[] i s1 hk rfl hok1
          ⟨_, [], x :: xs', hty2, InstLVec.empty _,
            by rw [ConLeche.Expr.instantiateList_nil]; exact hwty,
            denoteEList_ext hx1 _ _ hxs, hwxs⟩) ?_
        rintro r s4 ⟨hok4, hx4, hp4, hr⟩
        refine ⟨hok4, hx1.trans hx4, by rw [hp4, hp1], ?_⟩
        have := hr _ [] (x :: xs') hty2 (InstLVec.empty _)
          (denoteEList_ext hx1 _ _ hxs)
        rwa [ConLeche.Expr.instantiateList_nil] at this
    all_goals
      dsimp only
      obtain ⟨hne, hnb⟩ := denote_not_forallE_bvar hwf hv hh
        (fun _ _ h => nomatch h) (fun _ h => nomatch h)
      exact tpure ⟨hok, Ext.refl _, rfl, 0,
        iotaCertsFullFueled_notpi (instantiateList_not_forallE hne hnb)⟩
  · rw [dite_eq_right hi]
    have hnil : xs = [] := by
      have h0 : args.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      rw [h0] at hxs
      exact denoteEList_nil_inv hxs
    subst hnil
    exact tpure ⟨hok, Ext.refl _, rfl, 0, iotaCertsFullFueled_nil⟩

/-- con-leche: ConLeche/Kernel/Core.lean:251-259 iotaCertsFull — **THEOREM 1
for `iotaCertsFull`**, the empty-accumulator entry of `iotaCertsFullAux_go`,
in answer shape (its subject is `constTyAt`'s answer at its caller). -/
theorem iotaCertsFull_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (h : EIdx) (args : List EIdx) (s₀ : AState)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ tyx xs, denoteE s₀.store h = some tyx ∧ Expr.WScoped d tyx ∧
      Frontend.denoteEList s₀.store args = some xs ∧
      ∀ x ∈ xs, Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaCertsFull (coreKnot mode fe id fuel) fe d h args
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ tyx xs, denoteE s₀.store h = some tyx →
          Frontend.denoteEList s₀.store args = some xs →
          SimBOp (fun F => ConLeche.iotaCertsFullFueled mode env F d tyx xs)
            r; ⊤⦄ := by
  obtain ⟨tyx, xs, hh, hw, hxs, hwxs⟩ := hpre
  have hg := iotaCertsFullAux_go hsim d args.toArray _ _ h #[] 0 s₀
    rfl rfl hok ⟨tyx, [], xs, hh, InstLVec.empty _,
      by rw [ConLeche.Expr.instantiateList_nil]; exact hw,
      by simpa using hxs, hwxs⟩
  unfold ConRon.Arena.iotaCertsFull
  refine triple_mono hg ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, fun tyx' xs' e1 e2 => ?_⟩
  have := h4 tyx' [] xs' e1 (InstLVec.empty _) (by simpa using e2)
  rwa [ConLeche.Expr.instantiateList_nil] at this

/-- con-leche: none — a stored constructor denotes a constructor, with the
same two counts. -/
theorem denoteCI_ctorInfo_inv {st : EStore} {v : IConstantVal} {nP nF : Nat}
    {c : ConstantInfo}
    (h : Frontend.denoteCI st (.ctorInfo v nP nF) = some c) :
    ∃ cv, Frontend.denoteCV st v = some cv ∧ c = .ctorInfo cv nP nF := by
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨cv, hcv, rfl⟩ := h
  exact ⟨cv, hcv, rfl⟩

/-- con-leche: none — and the other direction: a stored constant that
denotes a constructor IS one (`projCert` decides a guard on it). -/
theorem denoteCI_ctor_inv {st : EStore} {ci : IConstantInfo} {cv : ConstantVal}
    {nP nF : Nat} (h : Frontend.denoteCI st ci = some (.ctorInfo cv nP nF)) :
    ∃ v, ci = .ctorInfo v nP nF := by
  cases ci with
  | ctorInfo v nP' nF' =>
    obtain ⟨_, _, hc⟩ := denoteCI_ctorInfo_inv h
    simp only [ConstantInfo.ctorInfo.injEq] at hc
    obtain ⟨_, rfl, rfl⟩ := hc
    exact ⟨v, rfl⟩
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | defnInfo v e hi =>
    obtain ⟨_, _, _, _, hc⟩ := denoteCI_defnInfo_inv h; simp at hc
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | indInfo v c =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases hc : Frontend.denoteCaps st c with
      | none => rw [hv, hc] at h; simp at h
      | some cc => rw [hv, hc] at h; simp at h
  | recInfo v mI rP rs =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases hr : Frontend.denoteRules st rs with
      | none => rw [hv, hr] at h; simp at h
      | some rr => rw [hv, hr] at h; simp at h

/-- con-leche: ConLeche/Kernel/Env.lean:686 Env.find? — a lookup answers a
constant carrying the name it was looked up at (the name search). -/
theorem env_find_name {n : ConLeche.Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  simp only [ConLeche.Env.find?] at h
  have := List.find?_some h
  simpa using this

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's HIT half at
a constructor. -/
theorem env_ctor_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {nm : ConLeche.Name} {icv : IConstantVal} {nP nF : Nat}
    (hn : denoteN s.store.ns c = some nm)
    (hfd : fe.find? c = some (.ctorInfo icv nP nF)) :
    ∃ dcv, Frontend.denoteCV s.store icv = some dcv ∧
      env.find? nm = some (.ctorInfo dcv nP nF) := by
  obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c _ hfd
  obtain rfl := Option.some.inj (hn'.symm.trans hn)
  obtain ⟨dcv, hdcv, rfl⟩ := denoteCI_ctorInfo_inv hci
  exact ⟨dcv, hdcv, hfind⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's MISS half at
a constructor. -/
theorem env_not_ctor_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {nm : ConLeche.Name} (hn : denoteN s.store.ns c = some nm)
    (hnd : ∀ v nP nF, fe.find? c ≠ some (.ctorInfo v nP nF)) :
    ∀ cv nP nF, env.find? nm ≠ some (.ctorInfo cv nP nF) := by
  intro cv nP nF hcon
  cases hf : fe.find? c with
  | none => rw [IFEnvOK.miss hok.state hok.ienv hn hf] at hcon; simp at hcon
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    rw [hfind] at hcon
    obtain rfl := Option.some.inj hcon
    obtain ⟨v, rfl⟩ := denoteCI_ctor_inv hci
    exact hnd v nP nF hf

/-! ### Vocabulary candidates for Bridge/Grind.lean (task #123): the constructor index

`Bridge/Grind.lean` §6's shape (`FindAt`, the definitions) at a CONSTRUCTOR:
is a lookup a constructor, its record, and the index's two halves at a
denoting name handle as one fact keyed by the invariant and the lookup. -/

/-- con-leche: none — is a stored lookup a constructor. -/
def iCtor? : Option IConstantInfo → Bool | some (.ctorInfo _ _ _) => true | _ => false
/-- con-leche: none — a stored constructor's record (a default elsewhere). -/
def iCtorVal : Option IConstantInfo → IConstantVal | some (.ctorInfo v _ _) => v | _ => default
/-- con-leche: none — a stored constructor's parameter count. -/
def iCtorNP : Option IConstantInfo → Nat | some (.ctorInfo _ n _) => n | _ => 0
/-- con-leche: none — a stored constructor's field count. -/
def iCtorNF : Option IConstantInfo → Nat | some (.ctorInfo _ _ n) => n | _ => 0
/-- con-leche: none — is an environment lookup a constructor. -/
def cCtor? : Option ConstantInfo → Bool | some (.ctorInfo _ _ _) => true | _ => false
/-- con-leche: none — a constructor's record. -/
def cCtorVal : Option ConstantInfo → ConstantVal | some (.ctorInfo v _ _) => v | _ => default

/-- con-leche: none — `iCtor?` at a constructor. -/
@[bridge_grind =] theorem iCtor?_ctor (v : IConstantVal) (a b : Nat) :
    iCtor? (some (.ctorInfo v a b)) = true := rfl
/-- con-leche: none — `iCtorVal` at a constructor. -/
@[bridge_grind =] theorem iCtorVal_ctor (v : IConstantVal) (a b : Nat) :
    iCtorVal (some (.ctorInfo v a b)) = v := rfl
/-- con-leche: none — a lookup that is a constructor IS one: what refutes a
`match`'s fall-through arm. -/
theorem iCtor?_eta {o : Option IConstantInfo} (h : iCtor? o = true) :
    o = some (.ctorInfo (iCtorVal o) (iCtorNP o) (iCtorNF o)) := by
  match o, h with
  | some (.ctorInfo _ _ _), _ => rfl
grind_pattern [bridge_grind] iCtor?_eta => iCtor? o

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index at a name handle
`c` denoting `nm`, at a constructor: the two lookups agree on being one, and
the records correspond. -/
def CtorAt (env : Env) (fe : IFEnv) (st : EStore) (c : NIdx) : Option ConLeche.Name → Prop
  | some nm => cCtor? (env.find? nm) = iCtor? (fe.find? c) ∧
      (iCtor? (fe.find? c) = true →
        Frontend.denoteCV st (iCtorVal (fe.find? c)) = some (cCtorVal (env.find? nm)))
  | none => True

/-- con-leche: none — a non-constructor environment lookup is `cCtor?`-false. -/
theorem cCtor?_of_not {o : Option ConstantInfo}
    (h : ∀ cv nP nF, o ≠ some (.ctorInfo cv nP nF)) : cCtor? o = false := by
  match o, h with
  | some (.ctorInfo cv a b), h => exact absurd rfl (h cv a b)
  | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.indInfo _ _), _
  | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _), _ | some (.projInfo _), _
  | none, _ => rfl

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `env_ctor_of_index` and
`env_not_ctor_of_index` as one fact at every lookup the program makes, keyed
by the invariant and the lookup. -/
theorem ctorAt {s : AState} (hok : CheckOK mode env fe s) (c : NIdx) :
    CtorAt env fe s.store c (denoteN s.store.ns c) := by
  cases hn : denoteN s.store.ns c with
  | none => trivial
  | some nm =>
  show _ ∧ _
  by_cases hc : iCtor? (fe.find? c) = true
  · have hf := iCtor?_eta hc
    obtain ⟨dcv, hdcv, hfind⟩ := env_ctor_of_index hok hn hf
    exact ⟨by rw [hc, hfind]; rfl, fun _ => by rw [hfind]; exact hdcv⟩
  · refine ⟨?_, fun h => absurd h hc⟩
    rw [Bool.not_eq_true] at hc
    rw [hc]
    exact cCtor?_of_not (env_not_ctor_of_index hok hn (fun v a b h => by
      rw [h] at hc; exact Bool.noConfusion hc))
grind_pattern [bridge_grind] ctorAt => CheckOK mode env fe s, fe.find? c

/-- con-leche: none — `CtorAt` at a denoting handle. -/
theorem CtorAt.some {st : EStore} {c : NIdx} {nm : ConLeche.Name}
    (H : CtorAt env fe st c (some nm)) :
    cCtor? (env.find? nm) = iCtor? (fe.find? c) ∧
      (iCtor? (fe.find? c) = true →
        Frontend.denoteCV st (iCtorVal (fe.find? c)) = some (cCtorVal (env.find? nm))) := H
grind_pattern [bridge_grind] CtorAt.some => CtorAt env fe st c (some nm)

/-! ## 5b. The arity certificate -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:43-46 peelPis — the successor
clause as ONE equation over the tag and the body projection. -/
theorem peelPis_succ_eq (k : Nat) (e : Expr) :
    Expr.peelPis (k + 1) e =
      if exprTag e = ETag.forallE then Expr.peelPis k (exprBody e) else none := by
  cases e <;> simp [Expr.peelPis, exprTag, exprBody, ETag.forallE, ETag.bvar, ETag.fvar,
    ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/PropRead.lean:43-46 peelPis — **THEOREM 1 for
`peelPis`** in answer shape: `RelEO` at con-leche's peel (task #123: a named
answer, read by `grind` as `MapRelO`). -/
theorem peelPis_specA (k : Nat) : ∀ (s₀ : AState) (h : EIdx), StoreWF s₀.store →
    (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ ConRon.Arena.peelPis k h
    ⦃fun r s' => s' = s₀ ∧ RelEO (Expr.peelPis k) s₀.store h s₀.store r; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ h _ hden
    sym only [bridge_grind, Expr.peelPis] => vcgen [ConRon.Arena.peelPis] <;> finish
  | succ k ih =>
    intro s₀ h hwf hden
    sym only [bridge_grind, peelPis_succ_eq] => vcgen [ConRon.Arena.peelPis, ih] <;> finish

/-- con-leche: ConLeche/Kernel/PropRead.lean:43-46 peelPis — **THEOREM 1 for
`peelPis`**: read-only, and the answer denotes con-leche's peel. -/
theorem peelPis_spec (s₀ : AState) (hwf : StoreWF s₀.store) :
    ∀ (k : Nat) (h : EIdx) (E : Expr), denoteE s₀.store h = some E →
      ⦃fun s => s = s₀⦄ ConRon.Arena.peelPis k h
      ⦃fun r s' => s' = s₀ ∧ denoteEO s₀.store r = some (Expr.peelPis k E); ⊤⦄ :=
  fun k h E hd => triple_mono (peelPis_specA k s₀ h hwf (by rw [hd]; rfl))
    (fun _ _ ⟨h1, h2⟩ => ⟨h1, h2 E hd⟩)

/-- con-leche: none — an optional handle's `isSome` is its denotation's. -/
theorem isSome_of_denoteEO {st : EStore} {r : Option EIdx} {v : Option Expr}
    (h : denoteEO st r = some v) : r.isSome = v.isSome := by
  cases r with
  | none => simp only [denoteEO, Option.some.injEq] at h; subst h; rfl
  | some j =>
    simp only [denoteEO, Option.map_eq_some_iff] at h
    obtain ⟨y, _, rfl⟩ := h; rfl
grind_pattern [bridge_grind] isSome_of_denoteEO => denoteEO st r, some v where
  guard denoteEO st r = some v

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:752-753 teleArityOk — the
arity test's answer at the denotations of the type and the spine. -/
def TeleArityPost : Option Expr → Option (List Expr) → Bool → Prop
  | some T, some xs, r => r = ConLeche.teleArityOk T xs
  | _, _, _ => True

/-- con-leche: none — `TeleArityPost` at denoting subjects. -/
@[bridge_grind =] theorem TeleArityPost.some_eq (T : Expr) (xs : List Expr) (r : Bool) :
    TeleArityPost (some T) (some xs) r = (r = ConLeche.teleArityOk T xs) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:752-753 teleArityOk — **THEOREM
1 for `teleArityOk`**: read-only, and the syntactic arity test agrees
(answer shape, `TeleArityPost`). -/
theorem teleArityOk_spec (s₀ : AState) (hwf : StoreWF s₀.store) (ty : EIdx)
    (args : List EIdx) (hT : (denoteE s₀.store ty).isSome = true)
    (hxs : (Frontend.denoteEList s₀.store args).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.teleArityOk ty args
    ⦃fun r s' => s' = s₀ ∧
        TeleArityPost (denoteE s₀.store ty) (Frontend.denoteEList s₀.store args) r; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.teleArityOk] =>
    vcgen [ConRon.Arena.teleArityOk, peelPis_specA] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:879-882 projCert — the function as
ONE equation over the environment's constructor projections. -/
@[bridge_grind =] theorem projCert_eq (cn : ConLeche.Name) (xs : List Expr) :
    ConLeche.projCert env cn xs =
      (cCtor? (env.find? cn) && ConLeche.teleArityOk (cCtorVal (env.find? cn)).type xs) := by
  simp only [ConLeche.projCert]
  generalize env.find? cn = o
  match o with
  | some (.ctorInfo _ _ _) => rfl
  | some (.axiomInfo _) | some (.thmInfo _) | some (.indInfo _ _) | some (.defnInfo _ _ _)
  | some (.recInfo _ _ _ _) | some (.projInfo _) | none => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:879-883 projCert — **THEOREM 1 for
the structural projection's certificate**: the constructor's stored type has
the spine's arity (`teleArityOk`, con-leche's task #342 L18).  Read-only.
`grind` reads the index through `CtorAt` and the type through `DenoteCV`. -/
theorem projCert_spec (s₀ : AState) (hok : CheckOK mode env fe s₀)
    (c : NIdx) (args : List EIdx) (cn : ConLeche.Name) (xs : List Expr)
    (hc : denoteN s₀.store.ns c = some cn)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projCert fe c args
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.projCert env cn xs; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.projCert, teleArityOk_spec] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:890-892 projCertAt — **THEOREM 1 for
`projCertAt`**: the verified mode checks the arity, the trusted mode nothing.
Read-only. -/
theorem projCertAt_spec (s₀ : AState) (hok : CheckOK mode env fe s₀)
    (verified : Bool) (c : NIdx) (args : List EIdx) (cn : ConLeche.Name)
    (xs : List Expr) (hc : denoteN s₀.store.ns c = some cn)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projCertAt fe verified c args
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.projCertAt env verified cn xs; ⊤⦄ := by
  cases verified with
  | true =>
    simp only [ConRon.Arena.projCertAt, ConLeche.projCertAt, ite_true]
    exact projCert_spec s₀ hok c args cn xs hc hargs
  | false =>
    simp only [ConRon.Arena.projCertAt, ConLeche.projCertAt, Bool.false_eq_true,
      ite_false]
    vcgen
    all_goals simp_all

/-! ## 6. The axiom census -/

section Census

#print axioms projTableName_spec
#print axioms projTableName_specC
#print axioms findProjAt
#print axioms IFEnv.findProj?_specA
#print axioms IFEnv.findProj?_spec
#print axioms IProjEntry.fireOk_spec
#print axioms ctorAt
#print axioms instantiateListFast_specC
#print axioms readNamesM_frame
#print axioms IProjEntry.typeAt_spec
#print axioms iotaCertsFullAux_go
#print axioms iotaCertsFull_spec
#print axioms peelPis_specA
#print axioms peelPis_spec
#print axioms teleArityOk_spec
#print axioms projCert_spec
#print axioms projCertAt_spec

end Census

end ConRon.Bridge.Core

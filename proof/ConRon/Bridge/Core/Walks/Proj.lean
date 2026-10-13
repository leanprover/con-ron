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

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

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
  vcgen [ConRon.Arena.projTableName, internNNode_spec]
  all_goals (bridge_peel; subst_vars
             grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
               nview_isSome_of_denote, Ext.trans, ConLeche.projTableName])

/-! ## 2. The shape clause con-leche's `ConstWF` half-records -/

/-! ## 3. The lookup -/

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
  vcgen [ConRon.Arena.IFEnv.findProj?, projTableName_spec (Tn := Tn)]
  all_goals (bridge_peel; subst_vars)
  case vc3 => exact hok.state.wf
  case vc4 => exact hT
  -- the index stores a TABLE at the reserved name
  case vc1 =>
    rename_i _s1 rn _s2 tbl hfind hwf2 hext hm hc hp hdn
    have hck : CheckOK mode env fe _s2 := hok.mono ⟨hwf2⟩ hext hc hp
    obtain ⟨nm, ci, hnm, hci, hfindE⟩ := hck.ienv.hit rn _ hfind
    obtain rfl : nm = ConLeche.projTableName Tn := by
      rw [hnm] at hdn; exact Option.some.inj hdn
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
    obtain ⟨pt, hpt, rfl⟩ := hci
    obtain ⟨hnf, _, _⟩ := denoteProjTable_fields hpt
    obtain ⟨hbsz, hgsz, -⟩ := hck.ienv.proj rn tbl hfind
    refine ⟨hck, hext, hm, hc, hp, ?_, ?_⟩
    · intro e he
      split at he
      · rename_i hlt
        obtain rfl := Option.some.inj he
        exact ⟨pt.entry i,
          denoteProjTable_entry hpt (by rw [hbsz]; exact hlt)
            (by rw [hgsz]; exact hlt),
          ConLeche.Env.findProj?_of_table hfindE (by rw [hnf]; exact hlt)⟩
      · exact absurd he (by simp)
    · intro he
      split at he
      · exact absurd he (by simp)
      · rename_i hlt
        simp only [ConLeche.Env.findProj?, hfindE]
        exact ite_eq_right (by rw [hnf]; exact hlt)
  -- the index stores no table there, so neither does the environment
  case vc2 =>
    rename_i _s1 rn _s2 hwf2 hext hm hc hp hdn hno
    have hck : CheckOK mode env fe _s2 := hok.mono ⟨hwf2⟩ hext hc hp
    refine ⟨hck, hext, hm, hc, hp, fun e he => absurd he (by simp),
      fun _ => ?_⟩
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
    vcgen [-readNamesM_spec, ConRon.Arena.readNamesM]
    bridge_peel; subst_vars
    exact ⟨ReadbackFrame.refl _, rfl⟩
  | cons a as ih =>
    vcgen [-readNamesM_spec, ConRon.Arena.readNamesM,
      readNameM_spec, ih]
    all_goals bridge_peel
    all_goals subst_vars
    all_goals first
      | assumption
      | (rename_i hst1 hf2 hden2 hm1 hp1 hc1 hden1 hN1
         have hf1 := ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN1
         rw [hst1] at hden2
         exact ⟨hf1.trans hf2,
           by simp only [Frontend.denoteNList, hden1, hden2]⟩)

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
  vcgen [lvlEq?_spec (mode := mode) (env := env) (fe := fe),
    -readNamesM_spec, readNamesM_frame]
  all_goals (bridge_peel; subst_vars)
  -- the two pin/invariant side goals
  case vc7 => exact hok.pins
  case vc6 => exact hok
  -- the three readback preconditions, each `CheckOK` carried to the state
  -- the previous call left
  case vc5 =>
    rename_i hck _ _ _ _
    exact hck.caches.readN
  case vc4 =>
    rename_i hck hf _ _ _ _ _
    exact (CheckOK.ofReadbackFrame hck hf).caches.readLs
  case vc3 =>
    rename_i hck hf2 _ hst _ hm _ _ hp hc _ hLs _
    exact (CheckOK.ofReadbackFrame hck
      (hf2.trans (ReadbackFrame.ofReadLs hst hm hp hc hLs))).caches.readL
  -- the guard DECLINES: the structure sort is not provably zero, so the rule
  -- fires unconditionally and con-leche's first disjunct is `true`
  case vc1 =>
    rename_i _s1 r _s2 hcond hck hst hp heq hzero
    obtain ⟨lu, lv, hlu, hlv, hr⟩ := heq
    rw [hss] at hlu
    rw [hzero] at hlv
    obtain rfl : lu = p.structSort := (Option.some.inj hlu).symm
    obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
    refine ⟨hck, hst, hp, ?_⟩
    simp only [ConLeche.ProjEntry.fireOk, ← hr, hcond, Bool.true_or]
  -- the guard FIRES: the structure sort IS provably zero, so con-leche's
  -- first disjunct is `false` and the verdict is the field sort's
  case vc2 =>
    rename_i _s4 rb _s3 hcond _s2 _s1 _s0 hck3 hf2 hlps3 hst21 hst10 hst34 hm21 hm10 hp34 heq3 hp21 hp10 hc21
      hc10 hus2 hLs1 hfs1 hL1 hzero
    have hf3 := ReadbackFrame.ofReadLs hst21 hm21 hp21 hc21 hLs1
    have hf4 := ReadbackFrame.ofReadL hst10 hm10 hp10 hc10 hL1
    have hf := (hf2.trans hf3).trans hf4
    refine ⟨CheckOK.ofReadbackFrame hck3 hf, hf.store.trans hst34,
      hf.pins.trans hp34, ?_⟩
    -- the three readbacks ARE con-leche's three arguments
    rw [hst34, hlps] at hlps3
    rw [hf2.store, hst34, hus] at hus2
    rw [hf3.store, hf2.store, hst34, hfs] at hfs1
    obtain rfl : ks = p.levelParams := (Option.some.inj hlps3).symm
    obtain rfl : vs = ls := (Option.some.inj hus2).symm
    obtain rfl : fs = p.fieldSort := (Option.some.inj hfs1).symm
    -- and the guard's own verdict is `some true`
    obtain ⟨lu, lv, hlu, hlv, hr⟩ := heq3
    rw [hss] at hlu
    rw [hzero] at hlv
    obtain rfl : lu = p.structSort := (Option.some.inj hlu).symm
    obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
    have hrb : p.structSort.isEquiv Level.zero = some true := by
      rw [← hr]; simpa using hcond
    simp only [ConLeche.ProjEntry.fireOk, hrb, beq_self_eq_true,
      Bool.not_true, Bool.false_or]

/-! ## 5. The two that waited on another tier — CLOSED (round 4) -/

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
  have hi := ExprOps.instLPFast_spec coreWalkFuel s₀ entry.levelParams us
    entry.body _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs
    hlps hus (by rw [hb]; rfl)
  have hl := fun (s : AState) (e : EIdx) =>
    ExprOps.instantiateListFast_spec coreWalkFuel s e (targs.toArray.push pe) 0
      (x :: xs.reverse)
  -- the push-order vector denotes `pe :: targs.reverse` (task #97-P6-15)
  have hvec : ExprOps.InstLVec s₀.store (targs.toArray.push pe)
      (x :: xs.reverse) := by
    unfold ExprOps.InstLVec
    simp only [Array.toList_push, List.reverse_cons,
      List.reverse_reverse]
    exact ExprOps.denoteEList_snoc hpe _ _ hargs
  vcgen [ConRon.Arena.IProjEntry.typeAt, hi, hl]
  all_goals (bridge_peel; subst_vars)
  -- `instantiateListFast_spec`'s three preconditions
  case vc2 => assumption
  case vc3 => exact hvec.ext ‹Ext _ _›
  case vc4 =>
    rename_i hrel
    rw [hrel _ hb]; rfl
  -- the postcondition
  case vc1 =>
    rename_i hst1 hst2 hx2 hL hc2 hLs hp2 hN _ hrel2 hx1 hc1 hp1 _ hrel1
    have hck1 := CheckOK.ofInstLP hok hst1 hx1 hL hLs hN hc1 hp1
    refine ⟨hck1.mono hst2 hx2 hc2 hp2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [hrel2 _ (hrel1 _ hb)]
    rfl


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
  sorry

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
  vcgen [hg]
  rename_i hpost
  obtain ⟨hck, hx, hp, hr⟩ := hpost
  refine ⟨hck, hx, hp, fun tyx' xs' h1 h2 => ?_⟩
  have := hr tyx' [] xs' h1 (InstLVec.empty _) (by simpa using h2)
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

/-- con-leche: ConLeche/Kernel/PropRead.lean:43-46 peelPis — **THEOREM 1 for
`peelPis`**: read-only, and the answer denotes con-leche's peel. -/
theorem peelPis_spec (s₀ : AState) (hwf : StoreWF s₀.store) :
    ∀ (k : Nat) (h : EIdx) (E : Expr), denoteE s₀.store h = some E →
      ⦃fun s => s = s₀⦄ ConRon.Arena.peelPis k h
      ⦃fun r s' => s' = s₀ ∧ denoteEO s₀.store r = some (Expr.peelPis k E); ⊤⦄
  | 0, h, E, hd => by
    rw [ConRon.Arena.peelPis]
    vcgen
    subst_vars
    exact ⟨rfl, by simp [denoteEO, hd, Expr.peelPis]⟩
  | k + 1, h, E, hd => by
    rw [ConRon.Arena.peelPis]
    by_cases htg : (h.tag == ETag.forallE) = true
    · rw [ite_eq_left htg]
      refine triple_seq (viewBind_spec s₀ h) ?_
      rintro o s1 ⟨hs1, rfl⟩
      subst s1
      cases hvb : s₀.store.viewBind h with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨ty, b⟩ := p
        dsimp only
        have hv := view_of_viewBind_forallE (by simpa using htg) hvb
        obtain ⟨T, B, rfl, _, hB⟩ := denote_forallE_inv hwf hv hd
        refine triple_mono (peelPis_spec s₀ hwf k b B hB) ?_
        rintro r s' ⟨rfl, hr⟩
        exact ⟨rfl, by simpa [Expr.peelPis] using hr⟩
    · rw [ite_eq_right htg]
      vcgen
      subst_vars
      refine ⟨rfl, ?_⟩
      obtain ⟨v, hv⟩ := denoteE_view hd
      have hnf := denote_not_forallE hwf hv hd (fun ty b hvb => htg (by
        rw [EStore.tagOf_of_view hv, hvb]; rfl))
      cases E <;> simp_all [denoteEO, Expr.peelPis]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:752-753 teleArityOk — **THEOREM
1 for `teleArityOk`**: read-only, and the syntactic arity test agrees. -/
theorem teleArityOk_spec (s₀ : AState) (hwf : StoreWF s₀.store) (ty : EIdx)
    (T : Expr) (args : List EIdx) (xs : List Expr)
    (hT : denoteE s₀.store ty = some T)
    (hxs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.teleArityOk ty args
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.teleArityOk T xs; ⊤⦄ := by
  have hlen := ExprOps.denoteEList_length _ _ hxs
  unfold ConRon.Arena.teleArityOk
  refine triple_seq (peelPis_spec s₀ hwf args.length ty T hT) ?_
  rintro o s1 ⟨rfl, ho⟩
  vcgen
  subst_vars
  refine ⟨rfl, ?_⟩
  simp only [ConLeche.teleArityOk, ← hlen]
  cases o <;> cases hp : Expr.peelPis args.length T <;>
    simp_all [denoteEO]

/-- con-leche: ConLeche/Kernel/Core.lean:879-883 projCert — **THEOREM 1 for
the structural projection's certificate**: the constructor's stored type has
the spine's arity (`teleArityOk`, con-leche's task #342 L18).  Read-only. -/
theorem projCert_spec (s₀ : AState) (hok : CheckOK mode env fe s₀)
    (c : NIdx) (args : List EIdx) (cn : ConLeche.Name) (xs : List Expr)
    (hc : denoteN s₀.store.ns c = some cn)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projCert fe c args
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.projCert env cn xs; ⊤⦄ := by
  unfold ConRon.Arena.projCert
  cases hfd : fe.find? c with
  | none =>
    dsimp only
    vcgen
    subst_vars
    exact ⟨rfl, by
      simp [ConLeche.projCert, IFEnvOK.miss hok.state hok.ienv hc hfd]⟩
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hfd
    obtain rfl := Option.some.inj (hn'.symm.trans hc)
    cases ci with
    | ctorInfo icv nP nF =>
      obtain ⟨dcv, hdcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      obtain ⟨_, _, hty⟩ := denoteCV_inv hdcv
      dsimp only
      refine triple_mono (teleArityOk_spec s₀ hok.state.wf icv.type dcv.type
        args xs hty hargs) ?_
      rintro r s' ⟨rfl, hr⟩
      exact ⟨rfl, by simp [ConLeche.projCert, hfind, hr]⟩
    | _ =>
      dsimp only
      vcgen
      subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.projCert, hfind]
      cases cc <;> first | rfl | (obtain ⟨v, hv⟩ := denoteCI_ctor_inv hci; cases hv)

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
#print axioms readNamesM_frame
#print axioms IProjEntry.typeAt_spec
#print axioms iotaCertsFullAux_go
#print axioms iotaCertsFull_spec
#print axioms peelPis_spec
#print axioms teleArityOk_spec
#print axioms projCert_spec
#print axioms projCertAt_spec

end Census

end ConRon.Bridge.Core

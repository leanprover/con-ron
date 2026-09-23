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
`CacheOK`, and — measured last round — the conjunct cannot be supplied from
the caller, by erasing the attribute or by passing a stronger theorem.

The fix belongs at `SpecsL.lean`'s spec, and `SpecsL.lean` is **not this
round's lane** (`Bridge/ExprOps/**` is being closed concurrently against
`readNamesM` through `instLPFast_spec`, and strengthening a spec under a live
proof is how a merge breaks).  So this module takes the *first* shape task
#97-P3-CoreWalks §3 describes and then discarded: **a body copy with no spec
of its own** (`readNamesMB`, `= rfl` to `readNamesM`), a frame theorem about
the copy, and a `simp only [readNamesM_eq]` in front of the walk's `mvcgen`.
It is twenty-five lines and it is entirely inside `Bridge/Core/**`.

**Ask for the coordinator**: one conjunct in `Bridge/SpecsL.lean`'s
`readNamesM_spec`,
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
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The reserved table name -/

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName — **THEOREM 1
for `projTableName`**: the handle the twin interns denotes con-leche's
reserved name `(T.str "projTable").num 0`.  Two `internNNode`s, in
`Bridge/Specs.lean`'s `internName_spec` shape. -/
theorem projTableName_spec (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (hwf : StoreWF s₀.store) (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projTableName T
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projTableName Tn)⌝⦄ := by
  mvcgen [ConRon.Arena.projTableName, internNNode_spec]
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
    ⦃fun s => ⌜s = s₀⌝⦄ fe.findProj? T i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ e, r = some e → ∃ p, denoteProjEntry s'.store e = some p ∧
          env.findProj? Tn i = some p) ∧
        (r = none → env.findProj? Tn i = none)⌝⦄ := by
  mvcgen [ConRon.Arena.IFEnv.findProj?, projTableName_spec]
  all_goals (bridge_peel; subst_vars)
  case vc2.hwf => exact hok.state.wf
  case vc3.hT => exact hT
  -- the index stores a TABLE at the reserved name
  case vc4 =>
    rename_i _s1 rn tbl hfind _s2 hwf2 hext hm hc hp hdn
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
        exact if_neg (by rw [hnf]; exact hlt)
  -- the index stores no table there, so neither does the environment
  case vc5 =>
    rename_i _s1 rn _s2 hwf2 hext hm hc hp hdn hno
    have hck : CheckOK mode env fe _s2 := hok.mono ⟨hwf2⟩ hext hc hp
    refine ⟨hck, hext, hm, hc, hp, fun e he => absurd he (by simp), ?_⟩
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

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `Arena/Monad.lean`'s
`readNamesM`, copied verbatim so that it carries no registered `@[spec]` and
a caller can state the frame for itself.  See the module note §2; the copy
goes the day `Bridge/SpecsL.lean`'s spec gains its `caches` conjunct. -/
def readNamesMB : List NIdx → AM (List ConLeche.Name)
  | [] => pure []
  | h :: hs => do
    let x ← readNameM h
    let xs ← readNamesMB hs
    pure (x :: xs)

/-- con-leche: none — the copy IS the function. -/
theorem readNamesM_eq : ConRon.Arena.readNamesM = readNamesMB := by
  funext hs
  induction hs with
  | nil => rfl
  | cons a as ih =>
    simp only [ConRon.Arena.readNamesM, readNamesMB, ih]

/-- con-leche: none — **the frame of a `readNamesM` call**, which
`Bridge/SpecsL.lean`'s registered spec does not carry.  One list induction
over `readNameM_spec`, whose own frame conjunct `Bridge/Specs.lean` has. -/
theorem readNamesMB_frame (s₀ : AState) (hs : List NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNamesMB hs
    ⦃⇓? xs s' => ⌜ReadbackFrame s₀ s' ∧
        Frontend.denoteNList s₀.store.ns hs = some xs⌝⦄ := by
  induction hs generalizing s₀ with
  | nil =>
    mvcgen [readNamesMB]
    bridge_peel; subst_vars
    exact ⟨ReadbackFrame.refl _, rfl⟩
  | cons a as ih =>
    mvcgen [readNamesMB, readNameM_spec, ih]
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
    ⦃fun s => ⌜s = s₀⌝⦄ entry.fireOk us
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = p.fireOk ls⌝⦄ := by
  obtain ⟨_hs, hlps, _hc, _hb, hfs, hss, _hi, _hnp, _hnf, _ho⟩ :=
    denoteProjEntry_inv hden
  simp only [ConRon.Arena.IProjEntry.fireOk, ConRon.Arena.zeroLevel,
    readNamesM_eq]
  mvcgen [lvlEq?_spec, readNamesMB_frame]
  all_goals (bridge_peel; subst_vars)
  -- the two pin/invariant side goals
  case vc1.hp => exact hok.pins
  case vc5.hok => exact hok
  -- the three readback preconditions, each `CheckOK` carried to the state
  -- the previous call left
  case vc7.hc =>
    rename_i _a1 _a2 _a3 _a4 _a5 hck _b1 _b2 _b3 _b4
    exact hck.caches.readN
  case vc8.hc =>
    rename_i _a1 _a2 _a3 _a4 _a5 _a6 _a7 hck hf _b1 _b2 _b3 _b4 _b5
    exact (CheckOK.ofReadbackFrame hck hf).caches.readLs
  case vc9.hc =>
    rename_i _a1 _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 hck hf2 _b1 hst _b2 hm _b3
      _b4 hp hc _b5 hLs _b6
    exact (CheckOK.ofReadbackFrame hck
      (hf2.trans (ReadbackFrame.ofReadLs hst hm hp hc hLs))).caches.readL
  -- the guard DECLINES: the structure sort is not provably zero, so the rule
  -- fires unconditionally and con-leche's first disjunct is `true`
  case vc6 =>
    rename_i _z _s1 r hcond _s2 hck hst hp heq hzero
    obtain ⟨lu, lv, hlu, hlv, hr⟩ := heq
    rw [hss] at hlu
    rw [hzero] at hlv
    obtain rfl : lu = p.structSort := (Option.some.inj hlu).symm
    obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
    refine ⟨hck, hst, hp, ?_⟩
    simp only [ConLeche.ProjEntry.fireOk, ← hr, hcond, Bool.true_or]
  -- the guard FIRES: the structure sort IS provably zero, so con-leche's
  -- first disjunct is `false` and the verdict is the field sort's
  case vc10 =>
    rename_i _z _s4 rb hcond _s3 ks _s2 vs _s1 fs _s0
      hck3 hf2 hlps3 hst21 hst10 hst34 hm21 hm10 hp34 heq3 hp21 hp10 hc21
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
    ⦃fun s => ⌜s = s₀⌝⦄ entry.typeAt us targs pe
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (p.typeAt ls xs x)⌝⦄ := by
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
  mvcgen [ConRon.Arena.IProjEntry.typeAt, hi, hl]
  all_goals (bridge_peel; subst_vars)
  case vc3 => intro s hst; intros; exact hst
  case vc4 => intro s _ hx; intros; exact hvec.ext hx
  case vc5 =>
    intro s _ _ _ _ _ _ _ _ _ hrel
    rw [hrel _ hb]; rfl
  case vc2 =>
    rename_i hst1 hL hLs hN hx1 _ hc1 hp1 _ hrel1
    intro hst2 hx2 _ hc2 hp2 _ hrel2
    have hck1 := CheckOK.ofInstLP hok hst1 hx1 hL hLs hN hc1 hp1
    refine ⟨hck1.mono hst2 hx2 hc2 hp2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [hrel2 _ (hrel1 _ hb)]
    rfl


/-! ## 5a. `iotaCerts` — the batched spine certificate (round 4)

`Arena/Core.lean`'s `iotaCertsAux` carries a PUSH-order accumulator of
pending substitutions (task #97-P6-9) and matches on the UN-instantiated
telescope, flushing at a `.bvar` head; con-leche's `iotaCerts` substitutes
eagerly.  The two meet through `ExprOps/Subst.lean`'s `InstLVec`: at every
step the arena's `(h, acc)` denotes con-leche's `tyx.instantiateList ws`.
This is con-leche's own `Verify/Cached/DiscC1.lean:131 iotaCertsCAux_sim`,
and the induction is its lexicographic measure `(args.size - i, acc.size)`,
spelled as two nested strong inductions. -/

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — the spine ran
out: certified. -/
theorem iotaCertsFueled_nil {F d : Nat} {lic : Bool} {ty : Expr} :
    ConLeche.iotaCertsFueled mode env F d lic ty [] = .ok true := by
  simp only [ConLeche.iotaCertsFueled, ConLeche.iotaCerts]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — a licensed
`.never` slot is skipped. -/
theorem iotaCertsFueled_skip {F d : Nat} {lic : Bool} {t b : Expr}
    {m : BinderMeta} {x : Expr} {xs : List Expr}
    (hg : (lic && m.pw.isNever) = true) :
    ConLeche.iotaCertsFueled mode env F d lic (.forallE t b m) (x :: xs) =
      ConLeche.iotaCertsFueled mode env F d lic (b.instantiate1 x) xs := by
  simp only [ConLeche.iotaCertsFueled, ConLeche.iotaCerts, hg, if_true]

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — a certified
slot: the argument's type agrees with the domain, and the walk continues. -/
theorem iotaCertsFueled_cert {F d : Nat} {lic : Bool} {t b : Expr}
    {m : BinderMeta} {x ta : Expr} {xs : List Expr}
    (hg : (lic && m.pw.isNever) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.isDefEqCore mode env F d ta t = .ok true) :
    ConLeche.iotaCertsFueled mode env F d lic (.forallE t b m) (x :: xs) =
      ConLeche.iotaCertsFueled mode env F d lic (b.instantiate1 x) xs := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).defeq d ta t = .ok true := h2
  simp only [ConLeche.iotaCertsFueled, ConLeche.iotaCerts, hg,
    Bool.false_eq_true, if_false, e1, e2, bind, Except.bind, if_true]

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — a slot whose
argument's type does not agree: declined. -/
theorem iotaCertsFueled_fail {F d : Nat} {lic : Bool} {t b : Expr}
    {m : BinderMeta} {x ta : Expr} {xs : List Expr}
    (hg : (lic && m.pw.isNever) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.isDefEqCore mode env F d ta t = .ok false) :
    ConLeche.iotaCertsFueled mode env F d lic (.forallE t b m) (x :: xs) =
      .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).defeq d ta t = .ok false := h2
  simp only [ConLeche.iotaCertsFueled, ConLeche.iotaCerts, hg,
    Bool.false_eq_true, if_false, e1, e2, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — arguments left
over and no binder to take them: declined. -/
theorem iotaCertsFueled_notpi {F d : Nat} {lic : Bool} {ty x : Expr}
    {xs : List Expr} (h : ∀ t b m, ty ≠ .forallE t b m) :
    ConLeche.iotaCertsFueled mode env F d lic ty (x :: xs) = .ok false := by
  cases ty <;> simp_all [ConLeche.iotaCertsFueled, ConLeche.iotaCerts] <;> rfl

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
theorem instantiateList_forallE {t b : Expr} {m : BinderMeta}
    {ws : List Expr} :
    (Expr.forallE t b m).instantiateList ws =
      .forallE (t.instantiateList ws) (b.instantiateList ws 1) m := by
  simp [Expr.instantiateList]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211 instantiateList — a head
that is neither a ∀ nor a loose variable keeps its constructor, so it is not
a ∀ afterwards either. -/
theorem instantiateList_not_forallE {e : Expr} {ws : List Expr}
    (hf : ∀ t b m, e ≠ .forallE t b m) (hb : ∀ k, e ≠ .bvar k) :
    ∀ t b m, e.instantiateList ws ≠ .forallE t b m := by
  cases e <;> simp_all [Expr.instantiateList]

/-- con-leche: none — a handle whose VIEW is neither a ∀ nor a loose
variable denotes neither. -/
theorem denote_not_forallE_bvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b m, v = .forallE ty b m → False)
    (hnb : ∀ k, v = .bvar k → False) :
    (∀ p q m, e ≠ .forallE p q m) ∧ ∀ k, e ≠ .bvar k := by
  cases v with
  | bvar i => exact absurd rfl (hnb i)
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨p, q, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m => exact absurd rfl (hne ty b m)
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:131 iotaCertsCAux_sim —
**the induction**, in ∃/∀ shape (the recursive calls' subjects are answers
of `instantiateListFast` and of the accumulator push). -/
theorem iotaCertsAux_go {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (lic : Bool) (args : Array EIdx) :
    ∀ (k m : Nat) (h : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState),
      args.size - i = k → acc.size = m → CheckOK mode env fe s₀ →
      (∃ tyx ws xs, denoteE s₀.store h = some tyx ∧
        ExprOps.InstLVec s₀.store acc ws ∧
        Expr.WScoped d (tyx.instantiateList ws) ∧
        Frontend.denoteEList s₀.store (args.toList.drop i) = some xs ∧
        ∀ x ∈ xs, Expr.WScoped d x) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.iotaCertsAux (coreKnot mode fe id fuel) fe d lic h acc
          args i
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∀ tyx ws xs, denoteE s₀.store h = some tyx →
            ExprOps.InstLVec s₀.store acc ws →
            Frontend.denoteEList s₀.store (args.toList.drop i) = some xs →
            SimBOp (fun F => ConLeche.iotaCertsFueled mode env F d lic
              (tyx.instantiateList ws) xs) r⌝⦄ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro h acc i s₀ hk hm hok hpre
  obtain ⟨tyx, ws, xs, hh, hacc, hwty, hxs, hwxs⟩ := hpre
  rw [ConRon.Arena.iotaCertsAux]
  by_cases hi : i < args.size
  · simp only [hi, dite_true]
    have ihF := fun (h' : EIdx) (acc' : Array EIdx) (s' : AState) =>
      ihk (args.size - (i + 1)) (by omega) acc'.size h' acc' (i + 1) s' rfl rfl
    have ihB := fun (h' : EIdx) (s' : AState) (hlt : 0 < m) =>
      ihm 0 hlt h' #[] i s' hk rfl
    have hio := hsim.inferIO'
    have hdq := hsim.defeq'
    have hl := fun (s : AState) (e : EIdx) =>
      ExprOps.instantiateListFast_spec coreWalkFuel s e acc 0 ws
    obtain ⟨x, xs', rfl, hx, hxs'⟩ := denoteEList_drop_cons hi hxs
    have hwx : Expr.WScoped d x := hwxs x (by simp)
    have hwxs' : ∀ z ∈ xs', Expr.WScoped d z := fun z hz => hwxs z (by simp [hz])
    -- the postcondition's three subjects are functional
    have huniq : ∀ (st : EStore) tyx' ws' xs'', Ext s₀.store st →
        denoteE st h = some tyx' → ExprOps.InstLVec st acc ws' →
        Frontend.denoteEList st (args.toList.drop i) = some xs'' →
        tyx' = tyx ∧ ws' = ws ∧ xs'' = x :: xs' := by
      intro st tyx' ws' xs'' hxt h1 h2 h3
      refine ⟨Option.some.inj (h1.symm.trans (denote_ext hh hxt)),
        InstLVec.unique h2 (hacc.ext hxt), ?_⟩
      rw [denoteEList_ext hxt _ _ hxs] at h3
      exact (Option.some.inj h3).symm
    mvcgen [ihF, ihB, hio, hdq, hl]
    all_goals (bridge_peel; subst_vars)
    -- the licensed SKIP
    case vc1 =>
      rename_i t' b' mb hg _ _ _ hview
      intro hck hxt hp hrec
      refine ⟨hck, hxt, hp, fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      obtain ⟨p, q, rfl, _, hq⟩ := denote_forallE_inv hok.state.wf hview hh
      obtain ⟨F, hF⟩ := hrec q (x :: ws') xs' hq (InstLVec.push hacc hx) hxs'
      refine ⟨F, ?_⟩
      dsimp only
      rw [instantiateList_forallE, iotaCertsFueled_skip hg,
        ← Expr.instantiateList_cons]
      exact hF
    case vc2 => intro s hs _; subst hs; exact hok
    case vc3 =>
      intro s hs hview; subst hs
      obtain ⟨p, q, rfl, _, hq⟩ := denote_forallE_inv hok.state.wf hview hh
      simp only [instantiateList_forallE, Expr.WScoped] at hwty
      refine ⟨q, x :: ws, xs', hq, InstLVec.push hacc hx, ?_, hxs', hwxs'⟩
      rw [Expr.instantiateList_cons]
      exact Expr.WScoped.instantiate1_gen hwx 0 hwty.2
    -- the certified slot: the preconditions
    case vc4.hok => exact hok.state
    case vc5.hvec => exact hacc
    case vc6.hden =>
      rename_i hview
      obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hok.state.wf hview hh
      rw [hp]; rfl
    case vc7.hok =>
      rename_i hst hxt _ hc hp _ _ _
      exact hok.mono hst hxt hc hp
    case vc8.hdw =>
      rename_i _ hxt _ _ _ _ _ _
      exact ⟨x, denote_ext hx hxt, hwx⟩
    case vc9.hok => rename_i hck _ _ _ _ _ _ _ _ _ _; exact hck
    case vc10.hda =>
      rename_i _ _ hx01 _ _ _ hsio _ _ _ _ _
      obtain ⟨v, hv, hw, _⟩ := hsio x (denote_ext hx hx01)
      exact ⟨v, hv, hw⟩
    case vc11.hdb =>
      rename_i _ _ _ hx12 _ _ _ _ _ _ hinst hview
      obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hok.state.wf hview hh
      simp only [instantiateList_forallE, Expr.WScoped] at hwty
      exact ⟨_, denote_ext (hinst p hp) hx12, hwty.1⟩
    case vc12 =>
      rename_i t' b' mb hg _ _ _ _ _ _ _ _ _ _ _ hx01 hx12 hx23 _ hp21 hsio hp32
        _ hp10 _ hinst hview hsdq
      intro hck hx34 hp43 hrec
      refine ⟨hck, ((hx01.trans hx12).trans hx23).trans hx34,
        by rw [hp43, hp32, hp21, hp10], fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      obtain ⟨p, q, rfl, hp, hq⟩ := denote_forallE_inv hok.state.wf hview hh
      obtain ⟨ta, hta, _, F1, hF1⟩ := hsio x (denote_ext hx hx01)
      obtain ⟨F2, hF2⟩ := hsdq ta _ hta (denote_ext (hinst p hp) hx12)
      have hx03 := (hx01.trans hx12).trans hx23
      obtain ⟨F3, hF3⟩ := hrec q (x :: ws') xs' (denote_ext hq hx03)
        (InstLVec.push (hacc.ext hx03) (denote_ext hx hx03))
        (denoteEList_ext hx03 _ _ hxs')
      refine ⟨F1 + F2 + F3, ?_⟩
      dsimp only
      rw [instantiateList_forallE,
        iotaCertsFueled_cert (Bool.eq_false_iff.mpr hg)
          (ConLeche.inferTypeIO_mono (by omega) hF1)
          (ConLeche.isDefEqCore_mono (by omega) hF2),
        ← Expr.instantiateList_cons]
      exact iotaCertsFueled_mono (by omega) hF3
    case vc13 => intro s hck _ _ _; exact hck
    case vc14 =>
      rename_i _ _ _ _ _ _ _ _ _ _ _ hx01 hx12 _ _ _ _ _ _ _ hview
      intro s _ hx23 _ _
      obtain ⟨p, q, rfl, _, hq⟩ := denote_forallE_inv hok.state.wf hview hh
      simp only [instantiateList_forallE, Expr.WScoped] at hwty
      have hx03 := (hx01.trans hx12).trans hx23
      refine ⟨q, x :: ws, xs', denote_ext hq hx03,
        InstLVec.push (hacc.ext hx03) (denote_ext hx hx03), ?_,
        denoteEList_ext hx03 _ _ hxs', hwxs'⟩
      rw [Expr.instantiateList_cons]
      exact Expr.WScoped.instantiate1_gen hwx 0 hwty.2
    -- the slot's type does not agree
    case vc15 =>
      rename_i t' b' mb hg _ _ _ _ _ rb hnb _ _ _ hck hx01 hx12 hx23 _ hp21 hsio
        hp32 hsdq _ hp10 _ hinst hview
      refine ⟨hck, (hx01.trans hx12).trans hx23, by rw [hp32, hp21, hp10],
        fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hok.state.wf hview hh
      obtain ⟨ta, hta, _, F1, hF1⟩ := hsio x (denote_ext hx hx01)
      obtain ⟨F2, hF2⟩ := hsdq ta _ hta (denote_ext (hinst p hp) hx12)
      obtain rfl : rb = false := by simpa using hnb
      refine ⟨F1 + F2, ?_⟩
      dsimp only
      rw [instantiateList_forallE]
      exact iotaCertsFueled_fail (Bool.eq_false_iff.mpr hg)
        (ConLeche.inferTypeIO_mono (by omega) hF1)
        (ConLeche.isDefEqCore_mono (by omega) hF2)
    -- a loose variable with nothing pending: declined
    case vc16 =>
      rename_i k hsz _ hview
      refine ⟨hok, Ext.refl _, rfl, fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      have hws : ws' = [] := by
        have h0 : acc = #[] := Array.eq_empty_of_size_eq_zero hsz
        subst h0
        exact InstLVec.unique hacc (InstLVec.empty _)
      subst hws
      rw [denote_bvar_inv hok.state.wf hview hh, ConLeche.Expr.instantiateList_nil]
      exact ⟨0, iotaCertsFueled_notpi (by simp)⟩
    -- the FLUSH: the pending substitution is applied and the walk looks again
    case vc17.hok => exact hok.state
    case vc18.hvec => exact hacc
    case vc19.hden => rw [hh]; rfl
    case vc20 =>
      rename_i _ _ _ _ _ _ _ hst hx01 _ hc10 hp10 _ hinst _
      intro hck hx12 hp21 hrec
      refine ⟨hck, hx01.trans hx12, by rw [hp21, hp10],
        fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      have := hrec _ [] (x :: xs') (hinst _ hh) (InstLVec.empty _)
        (denoteEList_ext hx01 _ _ hxs)
      rwa [ConLeche.Expr.instantiateList_nil] at this
    case vc21 =>
      rename_i hsz _ _ _
      intro s _ _ _ _ _ _ _
      exact Nat.pos_of_ne_zero hsz
    case vc22 =>
      intro s hst hx01 _ hc10 hp10 _ _
      exact hok.mono hst hx01 hc10 hp10
    case vc23 =>
      intro s _ hx01 _ _ _ _ hinst
      refine ⟨_, [], x :: xs', hinst _ hh, InstLVec.empty _, ?_,
        denoteEList_ext hx01 _ _ hxs, hwxs⟩
      rw [ConLeche.Expr.instantiateList_nil]; exact hwty
    -- any other head: declined on both sides
    case vc24 =>
      rename_i _ hnf hnb _ hview
      refine ⟨hok, Ext.refl _, rfl, fun tyx' ws' xs'' h1 h2 h3 => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq _ _ _ _ (Ext.refl _) h1 h2 h3
      obtain ⟨hf, hb⟩ := denote_not_forallE_bvar hok.state.wf hview hh hnf hnb
      exact ⟨0, iotaCertsFueled_notpi (instantiateList_not_forallE hf hb)⟩
  · simp only [hi, dite_false]
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, fun tyx ws xs _ _ hxs => ?_⟩
    have hnil : args.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hnil] at hxs
    obtain rfl := denoteEList_nil_inv hxs
    exact ⟨0, iotaCertsFueled_nil⟩

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — **THEOREM 1
for `iotaCerts`**, the empty-accumulator entry of `iotaCertsAux_go`, in
answer shape (its subject is `constTyAt`'s answer at every caller). -/
theorem iotaCerts_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (lic : Bool) (h : EIdx) (args : List EIdx) (s₀ : AState)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ tyx xs, denoteE s₀.store h = some tyx ∧ Expr.WScoped d tyx ∧
      Frontend.denoteEList s₀.store args = some xs ∧
      ∀ x ∈ xs, Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaCerts (coreKnot mode fe id fuel) fe d lic h args
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ tyx xs, denoteE s₀.store h = some tyx →
          Frontend.denoteEList s₀.store args = some xs →
          SimBOp (fun F => ConLeche.iotaCertsFueled mode env F d lic tyx xs)
            r⌝⦄ := by
  obtain ⟨tyx, xs, hh, hw, hxs, hwxs⟩ := hpre
  have hg := iotaCertsAux_go hsim d lic args.toArray _ _ h #[] 0 s₀
    rfl rfl hok ⟨tyx, [], xs, hh, InstLVec.empty _,
      by rw [ConLeche.Expr.instantiateList_nil]; exact hw,
      by simpa using hxs, hwxs⟩
  unfold ConRon.Arena.iotaCerts
  mvcgen [hg]
  intro hck hx hp hr
  refine ⟨hck, hx, hp, fun tyx' xs' h1 h2 => ?_⟩
  have := hr tyx' [] xs' h1 (InstLVec.empty _) (by simpa using h2)
  rwa [ConLeche.Expr.instantiateList_nil] at this

/-- con-leche: ConLeche/Kernel/Core.lean:912-947 projCert — the head is a
stored constructor: the certificate is `iotaCerts` at its instantiated
type. -/
theorem projCertFueled_ctor {F d : Nat} {lic : Bool} {cn : ConLeche.Name}
    {ls : List Level} {xs : List Expr} {cv : ConstantVal} {nP nF : Nat}
    (hf : env.find? cn = some (.ctorInfo cv nP nF)) :
    ConLeche.projCertFueled mode env F d lic cn ls xs =
      ConLeche.iotaCertsFueled mode env F d lic
        (cv.type.instantiateLevelParams cv.levelParams ls) xs := by
  simp only [ConLeche.projCertFueled, ConLeche.projCert, hf]

/-- con-leche: ConLeche/Kernel/Core.lean:912-947 projCert — anything else:
declined. -/
theorem projCertFueled_not {F d : Nat} {lic : Bool} {cn : ConLeche.Name}
    {ls : List Level} {xs : List Expr}
    (h : ∀ cv nP nF, env.find? cn ≠ some (.ctorInfo cv nP nF)) :
    ConLeche.projCertFueled mode env F d lic cn ls xs = .ok false := by
  simp only [ConLeche.projCertFueled, ConLeche.projCert]
  rfl

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
  | thmInfo v e =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases he : denoteE st e with
      | none => rw [hv, he] at h; simp at h
      | some xx => rw [hv, he] at h; simp at h
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

/-- con-leche: ConLeche/Kernel/Core.lean:912-947 projCert — **THEOREM 1 for
the structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)` fires
only after its constructor spine is certified against `C`'s stored type at the
redex's own levels.

**CLOSED** (round 4), on `constTyAt_spec'` and `iotaCerts_spec` above.
**Two preconditions were missing and are repaired** — exactly con-leche's own
`Verify/Cached/DiscC2.lean:442 projCertC_sim`'s: `EnvWF env` (the
constructor's stored type is closed, `const_ty_hasFvar`, which is what makes
the telescope well-scoped at `d`) and the arguments' well-scopedness at `d`
(the knot's `inferIO`/`defeq` slots take it at every slot).  Without them
the statement is not provable, and its caller (`whnfCoreBody`'s `.proj` arm)
holds both. -/
theorem projCert_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (henv : ConLeche.EnvWF env)
    (s₀ : AState) (d : Nat) (lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (cn : ConLeche.Name) (ls : List Level)
    (xs : List Expr) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns c = some cn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store args = some xs)
    (hwargs : ∀ x ∈ xs, Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCert (coreKnot mode fe id fuel) fe d lic c us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.projCertFueled mode env F d lic cn ls xs)
          b⌝⦄ := by
  have hct := fun (s : AState) (cv : IConstantVal) (u : LsIdx) =>
    constTyAt_spec' (mode := mode) (env := env) (fe := fe) s cv u
  have hic := fun (s : AState) (h : EIdx) (a : List EIdx) =>
    iotaCerts_spec hsim d lic h a s
  mvcgen [ConRon.Arena.projCert, hct, hic]
  all_goals (bridge_peel; subst_vars)
  case vc1.hok => exact hok
  case vc2.hpre =>
    rename_i _ _ _ hfd _
    obtain ⟨dcv, hdcv, hfind⟩ := env_ctor_of_index hok hc hfd
    have hname : dcv.name = cn := env_find_name hfind
    exact ⟨cn, ls, _, by rw [denoteCV_name hdcv, hname], hus, hfind, hdcv⟩
  case vc3 =>
    rename_i _ _ _ hfd _ _ _ _ _ _ _ _ hct'
    intro hck hx hp hcert
    obtain ⟨dcv, hdcv, hfind⟩ := env_ctor_of_index hok hc hfd
    have hname : dcv.name = cn := env_find_name hfind
    have hty := hct' cn ls _ (by rw [denoteCV_name hdcv, hname]) hus hfind
    obtain ⟨F, hF⟩ := hcert _ xs hty (denoteEList_ext ‹_› _ _ hargs)
    refine ⟨hck, ‹Ext _ _›.trans hx, hp.trans ‹_›, F, ?_⟩
    dsimp only
    rw [projCertFueled_ctor hfind]
    exact hF
  case vc4 => intro s hck _ _ _; exact hck
  case vc5 =>
    rename_i _ _ _ hfd _ _
    intro s _ hx _ hct'
    obtain ⟨dcv, hdcv, hfind⟩ := env_ctor_of_index hok hc hfd
    have hname : dcv.name = cn := env_find_name hfind
    refine ⟨_, _, hct' cn ls _ (by rw [denoteCV_name hdcv, hname]) hus hfind,
      Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls),
      denoteEList_ext hx _ _ hargs, hwargs⟩
  case vc6 =>
    rename_i hnd
    exact ⟨hok, Ext.refl _, rfl, 0,
      projCertFueled_not (env_not_ctor_of_index hok hc hnd)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:949-961 projCertAt — **THEOREM 1 for
`projCertAt`**: the fire certificate of a projection, gated on
`mode.verifiedChecks`.  **CLOSED** (round 4; moved here from
`Walks/Owed.lean`): the `verified = false` arm is `pure true` on both sides,
the `true` arm is `projCert_spec`, and the statement gains the same two
missing preconditions (`EnvWF env`, the arguments' scope). -/
theorem projCertAt_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (henv : ConLeche.EnvWF env)
    (s₀ : AState) (d : Nat) (verified lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (cn : ConLeche.Name) (ls : List Level)
    (xs : List Expr) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns c = some cn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store args = some xs)
    (hwargs : ∀ x ∈ xs, Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCertAt (coreKnot mode fe id fuel) fe d verified lic c
        us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp
          (fun F => ConLeche.projCertAtFueled mode env F d verified lic cn ls
            xs) b⌝⦄ := by
  cases verified with
  | true =>
    have hp := projCert_spec hsim henv s₀ d lic c us args cn ls xs hok hc hus
      hargs hwargs
    simp only [ConRon.Arena.projCertAt, if_true]
    mvcgen [hp]
  | false =>
    simp only [ConRon.Arena.projCertAt, Bool.false_eq_true, if_false]
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, 0, rfl⟩

/-! ## 6. The axiom census -/

section Census

#print axioms projTableName_spec
#print axioms readNamesM_eq
#print axioms IProjEntry.typeAt_spec
#print axioms iotaCertsAux_go
#print axioms iotaCerts_spec
#print axioms projCert_spec
#print axioms projCertAt_spec

end Census

end ConRon.Bridge.Core

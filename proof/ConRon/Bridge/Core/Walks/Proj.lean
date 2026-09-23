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
| `IProjEntry.typeAt_spec` | the `.proj` node's type | stated; waits on `ExprOps.instLPFast_spec` / `instantiateListFast_spec` |
| `projCert_spec` | the structural projection's certificate | stated; waits on `constTyAt_spec` and `iotaCerts_spec` |

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

/-! ## 5. The two that wait on another tier -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt —
**THEOREM 1 for the type of a `.proj` node at a tower-backed entry**: the
stored body, level-instantiated at the subject type's levels, with the
subject type's arguments and the subject substituted for its `numParams + 1`
loose variables in ONE traversal.

**OPEN**, and on the `ExprOps` tier alone: the twin is `instLPFast` followed
by `instantiateListFast` on the push-order array `targs.toArray.push pe`
(task #97-P6-15's accumulator ruling), so it needs
`Bridge/ExprOps/Owed.lean`'s `instLPFast_spec` and
`Bridge/ExprOps/Inst1.lean`'s `instantiateList_spec`, plus con-leche's own
`Expr.instantiateList` identification of `pe :: targs.reverse` with the
pushed array.  Nothing else: the entry's denotation is now in hand. -/
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


/-- con-leche: ConLeche/Kernel/Core.lean:912-947 projCert — **THEOREM 1 for
the structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)` fires
only after its constructor spine is certified against `C`'s stored type at the
redex's own levels.

**OPEN**: two callee rules, `Bridge/Core/Walks/Cached.lean`'s `constTyAt_spec`
(itself waiting on `ExprOps.instLPFast_spec`) and an `iotaCerts_spec` this
tier does not yet have — `iotaCerts` is the batched accumulator walk
(task #97-P6-9), identified against the chained spec by con-leche's
`Verify/Cached/DiscC1.lean:131 iotaCertsCAux_sim`.  Its fuel merge IS in hand:
`Bridge/Core/Walks/Mono.lean`'s `iotaCertsFueled_mono`. -/
theorem projCert_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (cn : ConLeche.Name) (ls : List Level)
    (xs : List Expr) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns c = some cn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCert (coreKnot mode fe id fuel) fe d lic c us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.projCertFueled mode env F d lic cn ls xs)
          b⌝⦄ := by
  sorry

/-! ## 6. The axiom census -/

section Census

#print axioms projTableName_spec
#print axioms readNamesM_eq
#print axioms IProjEntry.typeAt_spec

end Census

end ConRon.Bridge.Core

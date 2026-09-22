/-
# `ConRon.Bridge.Checker.DeclVal` — `DeclCheck`'s value checks and the three pin gates

`Arena/DeclCheck.lean` is the twin of `ConLeche/Kernel/DeclCheck.lean` plus the
three value-kind checks of `ConLeche/Kernel/Checker.lean:32-107`, and this
module is its bridge tier.  Four groups, and they are exactly the four things
`Bridge/Checker/Decl.lean`'s `defn` / `thm` / `opaque` arms call after
`checkConstantVal`:

1. **the three value checks** — `checkDefnVal`, `checkThmVal`,
   `checkOpaqueVal`.  Each is `installValue` plus one inference and one
   conversion, and each ends in an `IFEnv.push`, so each concludes `Pushed`
   and `Bridge/Checker/Inv.lean`'s **`StepOK env' fe' s'`** for the extended
   environment — the index answers, the environment is well formed, the index
   is its list's index, and it denotes.  Their state frame is `CoreStep` and
   not `StateOK` (task #97-P3-Checker-2): each CALLS the core, so the caches
   move, and what survives is the invariant at the environment the core ran at
   — which is the pre-insertion one, exactly as `checkConstantVal_bridge`
   concludes.  `StepOK` is what the two pin gates below read `fe2` for;
2. **the structural-`Nat` gate** — `natOpGuard` / `natOpStoredOkAll` /
   `certifyNatEqs`, run in the PRE-insertion environment with the operation's
   self-references replaced by its stored value;
3. **the `Nat.div`/`Nat.mod` variant gate** — `checkDivModPin`, whose loop is
   the one consumer of `Bridge/Checker/Base.lean`'s `orElseAttempt_run`;
4. **the compiler-trust gate** — `checkReducePin`.

**Why the pin gates are not `Bridge/Checker/Arms.lean`'s business.**  Each of
them runs AFTER the value check has already extended the environment, at the
extended index `fe2` and the pre-insertion one `fe` at once — con-leche's
`checkDivModPin ops pins env env2 c` and `checkReducePin ops env env2 c value`
take both for the same reason.  So each needs two invariants at once, which is
a shape nothing else in the tier has, and stating them here keeps the arms
uniform.

**What the second one is, corrected** (task #97-P3-Checker-2, named in task
#97-P3-Checker-3).  The round that stated these asked for
`FoldOK μ env2 fe2 s` — and `FoldOK` carries `PersIFEnv fe2`, which is
**false**: `fe2` is the environment the value check has just extended INSIDE
the per-declaration bracket, so the constant it holds carries a freshly
interned, hence scratch, type.  It is task #97-P3-Ind's finding at a second
site.  What the gates actually read `fe2` for is `reduceStoredOk fe2 c` /
`divModEnvGuard fe2 c`, two index lookups and no core call, so the clause they
need is **`StepOK env2 fe2 s`** — `Bridge/Checker/Inv.lean`'s name for exactly
that, and what the three value checks above now hand back.

**Both gates only ever DECLINE or pass.**  Neither installs anything: their
result is `Unit` on both sides, and the environment the arm returns is the one
the value check produced.  That is why their bridge theorems have no
environment clause at all — they are the cheapest statements of the tier and
the most expensive proofs, because the certificates they check are pinned
terms the core must run on.
-/
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Decl

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## One fuel per arm

Each of the six is con-leche's own `*_datF` read through `FueledM`'s
monotonicity, exactly as `Bridge/Checker/Mono.lean`'s `checkDecl_mono` is: an
arm composes two or three of these and needs them all at one fuel. -/

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:857 checkDefnVal_datF. -/
theorem checkDefnVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {hint : ReducibilityHint} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDefnVal (ConLeche.fueledOps μ F) env c x hint
      = .ok env') :
    ConLeche.checkDefnVal (ConLeche.fueledOps μ F') env c x hint = .ok env' := by
  rw [← ConLeche.checkDefnVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDefnVal (ConLeche.fueledOpsM μ) env c x hint).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:864 checkThmVal_datF. -/
theorem checkThmVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    ConLeche.checkThmVal (ConLeche.fueledOps μ F') env c x = .ok env' := by
  rw [← ConLeche.checkThmVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkThmVal (ConLeche.fueledOpsM μ) env c x).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:871 checkOpaqueVal_datF. -/
theorem checkOpaqueVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F') env c x = .ok env' := by
  rw [← ConLeche.checkOpaqueVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkOpaqueVal (ConLeche.fueledOpsM μ) env c x).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:878 certifyNatEqs_datF. -/
theorem certifyNatEqs_mono {μ : CheckMode} {env : Env}
    {xs : List (Expr × Expr)} {r : Bool} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs = .ok r) :
    ConLeche.certifyNatEqs (ConLeche.fueledOps μ F') env xs = .ok r := by
  rw [← ConLeche.certifyNatEqs_datF (mode := μ)] at h ⊢
  exact (ConLeche.certifyNatEqs (ConLeche.fueledOpsM μ) env xs).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:954 checkDivModPin_datF. -/
theorem checkDivModPin_mono {μ : CheckMode} {pinsP : List NatOpPinSet}
    {env env2 : Env} {nm : ConLeche.Name} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
      = .ok ()) :
    ConLeche.checkDivModPin (ConLeche.fueledOps μ F') pinsP env env2 nm
      = .ok () := by
  rw [← ConLeche.checkDivModPin_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDivModPin (ConLeche.fueledOpsM μ) pinsP env env2 nm).property
    hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:965 checkReducePin_datF. -/
theorem checkReducePin_mono {μ : CheckMode} {env env2 : Env}
    {nm : ConLeche.Name} {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
      = .ok ()) :
    ConLeche.checkReducePin (ConLeche.fueledOps μ F') env env2 nm x = .ok () := by
  rw [← ConLeche.checkReducePin_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkReducePin (ConLeche.fueledOpsM μ) env env2 nm x).property
    hle h

/-! ## The three value checks -/

/-- con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal — a
definition's value against its checked constant, returning the pushed index.

`sorry`: `installValue_bridge` (`Bridge/Checker/Split.lean`),
`KnotSpec.infer`, `KnotSpec.defeq`, then `IFEnv.push`.  Task
#97-P3-Checker's sorry list, item 22. -/
theorem checkDefnVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {hint : ReducibilityHint} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkDefnVal μ fe cv value hint s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkDefnVal (ConLeche.fueledOps μ F) env c x hint = .ok env' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal — **a theorem is
stored by its statement**: the constant keeps the record's RAW value as an
unread datum and the annotated value is a witness, checked and discarded.

`sorry`: `KnotSpec.infer`, `EnsureSortSpec.ensureSort`, the
is-a-proposition test (`lvlEq?` through `CacheOK.lvlEq`),
`installValue_bridge`, `KnotSpec.defeq`.  Task #97-P3-Checker's sorry
list, item 22. -/
theorem checkThmVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkThmVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal — the
theorem check without the is-a-proposition requirement; the result is stored
as an `axiomInfo`.

`sorry`: as `checkDefnVal_bridge`.  Task #97-P3-Checker's sorry list,
item 22. -/
theorem checkOpaqueVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkOpaqueVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  sorry

/-! ## The structural-`Nat` gate

Six readers and one certifier.  None of the six calls the core — they read the
environment index and intern pinned literals — so each has `PinStep`'s frame
and an answer relation, and the certifier alone is a `CoreStep`. -/

/-- con-leche: none — a list of equation PAIRS denotes, pointwise.  The
`certifyNatEqs` chain is stated with it rather than with the membership shape
the round that stated it used, because the recursion is positional: the arena
certifies the `i`-th pair against con-leche's `i`-th (task
#97-P3-Checker-2). -/
def EqPairsDenote (st : EStore) :
    List (EIdx × EIdx) → List (Expr × Expr) → Prop
  | [], [] => True
  | p :: ps, q :: qs =>
    denoteE st p.1 = some q.1 ∧ denoteE st p.2 = some q.2 ∧
      EqPairsDenote st ps qs
  | _, _ => False

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:475-481 natOpNames — the seven
structural fast-path operations, off the pin table.

**PROVED** (task #97-P3-Checker-3): seven `pinAt_run`s, in
`reservedBasisNames_run`'s shape and under its rule — the seven facts are
carried separately and the list is assembled once, at the end, against the
literal the `do`-block returns.  A pin read leaves the state alone, so there
is nothing to transport and the frame is an equation. -/
theorem natOpNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natOpNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natOpNames := by
  simp only [Arena.natOpNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl g7
  rw [e7] at r7
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r7
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames — the
eight WF-recursive operations, off the pin table.

**PROVED** (task #97-P3-Checker-3): `natOpNames_run`'s proof, one slot
longer. -/
theorem natDivModNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natDivModNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natDivModNames := by
  simp only [Arena.natDivModNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natModName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl g7
  rw [e7] at r7
  obtain ⟨n8, t8, g8, r8⟩ := AM.bind_ok r7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl g8
  rw [e8] at r8
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r8
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, d8, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps — the
operations (transitively) involved in `c`'s recurrences.  The twin's dispatch
is a chain of HANDLE comparisons where con-leche's is a chain of name
comparisons, so the answer is exact for `denoteN_inj`'s reason.

**PROVED** (task #97-P3-Checker-3): fifteen `pinAt_run`s, `beq_handle_iff` at
each of the fifteen tests, and the sixteen arms.  A pin read leaves the state
alone, so every arm's frame is the same `rfl`-shaped record and the only
content is which list comes out.

**The statement gained `PinsOK s`** — it read the pin table fifteen times and
did not ask for it, so as stated it was not provable (nothing made the handles
`pinAt` hands back denote anything).  It is free at the one call site
(`Bridge/Checker/Arms.lean`'s `defn` arm has `FoldOK`, hence
`hok.check.pins`). -/
theorem natOpDeps_run {cn : NIdx} {nm : ConLeche.Name} {ds : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpDeps cn s = .ok (ds, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ denoteNL s'.store ds (ConLeche.natOpDeps nm) := by
  simp only [Arena.natOpDeps] at hr
  -- fifteen pin reads; none of them moves the state
  obtain ⟨hpr, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, d0⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl q0
  rw [p0] at w0
  obtain ⟨had, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨p1, d1⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl q1
  rw [p1] at w1
  obtain ⟨hsu, u2, q2, w2⟩ := AM.bind_ok w1
  obtain ⟨p2, d2⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl q2
  rw [p2] at w2
  obtain ⟨hmu, u3, q3, w3⟩ := AM.bind_ok w2
  obtain ⟨p3, d3⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl q3
  rw [p3] at w3
  obtain ⟨hpo, u4, q4, w4⟩ := AM.bind_ok w3
  obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl q4
  rw [p4] at w4
  obtain ⟨hbe, u5, q5, w5⟩ := AM.bind_ok w4
  obtain ⟨p5, d5⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl q5
  rw [p5] at w5
  obtain ⟨hbl, u6, q6, w6⟩ := AM.bind_ok w5
  obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl q6
  rw [p6] at w6
  obtain ⟨hdi, u7, q7, w7⟩ := AM.bind_ok w6
  obtain ⟨p7, d7⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl q7
  rw [p7] at w7
  obtain ⟨hmo, u8, q8, w8⟩ := AM.bind_ok w7
  obtain ⟨p8, d8⟩ := pinAt_run (x := ConLeche.natModName) hp rfl q8
  rw [p8] at w8
  obtain ⟨hgc, u9, q9, w9⟩ := AM.bind_ok w8
  obtain ⟨p9, d9⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl q9
  rw [p9] at w9
  obtain ⟨hla, u10, q10, w10⟩ := AM.bind_ok w9
  obtain ⟨p10, d10⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl q10
  rw [p10] at w10
  obtain ⟨hlo, u11, q11, w11⟩ := AM.bind_ok w10
  obtain ⟨p11, d11⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl q11
  rw [p11] at w11
  obtain ⟨hxo, u12, q12, w12⟩ := AM.bind_ok w11
  obtain ⟨p12, d12⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl q12
  rw [p12] at w12
  obtain ⟨hsl, u13, q13, w13⟩ := AM.bind_ok w12
  obtain ⟨p13, d13⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl q13
  rw [p13] at w13
  obtain ⟨hsr, u14, q14, w14⟩ := AM.bind_ok w13
  obtain ⟨p14, d14⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl q14
  rw [p14] at w14
  -- the frame every arm shares
  have frame : ∀ out : List NIdx, (pure out : AM (List NIdx)) s = .ok (ds, s') →
      denoteNL s.store out (ConLeche.natOpDeps nm) →
      StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
        s'.pins = s.pins ∧ denoteNL s'.store ds (ConLeche.natOpDeps nm) := by
    intro out hpure hd
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hpure
    exact ⟨hok, Ext.refl _, rfl, rfl, hd⟩
  -- a handle test IS a name test
  have b0 : (cn == hpr) = true ↔ nm = ConLeche.natPredName := beq_handle_iff hok.wf hn d0
  have b1 : (cn == had) = true ↔ nm = ConLeche.natAddName := beq_handle_iff hok.wf hn d1
  have b2 : (cn == hsu) = true ↔ nm = ConLeche.natSubName := beq_handle_iff hok.wf hn d2
  have b3 : (cn == hmu) = true ↔ nm = ConLeche.natMulName := beq_handle_iff hok.wf hn d3
  have b4 : (cn == hpo) = true ↔ nm = ConLeche.natPowName := beq_handle_iff hok.wf hn d4
  have b5 : (cn == hbe) = true ↔ nm = ConLeche.natBeqName := beq_handle_iff hok.wf hn d5
  have b6 : (cn == hbl) = true ↔ nm = ConLeche.natBleName := beq_handle_iff hok.wf hn d6
  have b7 : (cn == hdi) = true ↔ nm = ConLeche.natDivName := beq_handle_iff hok.wf hn d7
  have b8 : (cn == hmo) = true ↔ nm = ConLeche.natModName := beq_handle_iff hok.wf hn d8
  have b9 : (cn == hgc) = true ↔ nm = ConLeche.natGcdName := beq_handle_iff hok.wf hn d9
  have b10 : (cn == hla) = true ↔ nm = ConLeche.natLandName := beq_handle_iff hok.wf hn d10
  have b11 : (cn == hlo) = true ↔ nm = ConLeche.natLorName := beq_handle_iff hok.wf hn d11
  have b12 : (cn == hxo) = true ↔ nm = ConLeche.natXorName := beq_handle_iff hok.wf hn d12
  have b13 : (cn == hsl) = true ↔ nm = ConLeche.natShiftLeftName := beq_handle_iff hok.wf hn d13
  have b14 : (cn == hsr) = true ↔ nm = ConLeche.natShiftRightName := beq_handle_iff hok.wf hn d14
  -- the sixteen arms
  rcases AM.ite_ok w14 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · exact frame _ a0 (by simp only [ConLeche.natOpDeps, if_pos (b0.mp y0)]; exact ⟨d0, trivial⟩)
  have nb0 : ¬ (nm = ConLeche.natPredName) := fun h => z0 (b0.mpr h)
  rcases AM.ite_ok v0 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · exact frame _ a1 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_pos (b1.mp y1)]; exact ⟨d1, trivial⟩)
  have nb1 : ¬ (nm = ConLeche.natAddName) := fun h => z1 (b1.mpr h)
  rcases AM.ite_ok v1 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · exact frame _ a2 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]; exact ⟨d0, d2, trivial⟩)
  have nb2 : ¬ (nm = ConLeche.natSubName) := fun h => z2 (b2.mpr h)
  rcases AM.ite_ok v2 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · exact frame _ a3 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]; exact ⟨d1, d3, trivial⟩)
  have nb3 : ¬ (nm = ConLeche.natMulName) := fun h => z3 (b3.mpr h)
  rcases AM.ite_ok v3 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · exact frame _ a4 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]; exact ⟨d1, d3, d4, trivial⟩)
  have nb4 : ¬ (nm = ConLeche.natPowName) := fun h => z4 (b4.mpr h)
  rcases AM.ite_ok v4 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · exact frame _ a5 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]; exact ⟨d5, trivial⟩)
  have nb5 : ¬ (nm = ConLeche.natBeqName) := fun h => z5 (b5.mpr h)
  rcases AM.ite_ok v5 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · exact frame _ a6 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]; exact ⟨d6, trivial⟩)
  have nb6 : ¬ (nm = ConLeche.natBleName) := fun h => z6 (b6.mpr h)
  rcases AM.ite_ok v6 with ⟨y7, a7⟩ | ⟨z7, v7⟩
  · exact frame _ a7 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_pos (b7.mp y7)]; exact ⟨d0, d2, d6, d7, trivial⟩)
  have nb7 : ¬ (nm = ConLeche.natDivName) := fun h => z7 (b7.mpr h)
  rcases AM.ite_ok v7 with ⟨y8, a8⟩ | ⟨z8, v8⟩
  · exact frame _ a8 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_pos (b8.mp y8)]; exact ⟨d0, d2, d6, d8, trivial⟩)
  have nb8 : ¬ (nm = ConLeche.natModName) := fun h => z8 (b8.mpr h)
  rcases AM.ite_ok v8 with ⟨y9, a9⟩ | ⟨z9, v9⟩
  · exact frame _ a9 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_pos (b9.mp y9)]; exact ⟨d6, d8, d9, trivial⟩)
  have nb9 : ¬ (nm = ConLeche.natGcdName) := fun h => z9 (b9.mpr h)
  rcases AM.ite_ok v9 with ⟨y10, a10⟩ | ⟨z10, v10⟩
  · exact frame _ a10 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_pos (b10.mp y10)]; exact ⟨d1, d3, d6, d7, d8, d10, trivial⟩)
  have nb10 : ¬ (nm = ConLeche.natLandName) := fun h => z10 (b10.mpr h)
  rcases AM.ite_ok v10 with ⟨y11, a11⟩ | ⟨z11, v11⟩
  · exact frame _ a11 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_pos (b11.mp y11)]; exact ⟨d1, d2, d3, d6, d7, d8, d11, trivial⟩)
  have nb11 : ¬ (nm = ConLeche.natLorName) := fun h => z11 (b11.mpr h)
  rcases AM.ite_ok v11 with ⟨y12, a12⟩ | ⟨z12, v12⟩
  · exact frame _ a12 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_pos (b12.mp y12)]; exact ⟨d1, d3, d6, d7, d8, d12, trivial⟩)
  have nb12 : ¬ (nm = ConLeche.natXorName) := fun h => z12 (b12.mpr h)
  rcases AM.ite_ok v12 with ⟨y13, a13⟩ | ⟨z13, v13⟩
  · exact frame _ a13 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_pos (b13.mp y13)]; exact ⟨d2, d3, d6, d13, trivial⟩)
  have nb13 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z13 (b13.mpr h)
  rcases AM.ite_ok v13 with ⟨y14, a14⟩ | ⟨z14, v14⟩
  · exact frame _ a14 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_neg nb13, if_pos (b14.mp y14)]; exact ⟨d2, d6, d7, d14, trivial⟩)
  have nb14 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z14 (b14.mpr h)
  exact frame _ v14 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_neg nb13, if_neg nb14]; exact trivial)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpGuard) — the
structural-`Nat` environment guard is con-leche's at the denoted environment.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4 — the same
defect as `natOpDeps_run`'s above, found by the grep that round asks for):
`natOpGuard` reads eight pins (`natLitSupported`'s three, `natBeqName`,
`natBleName`, `natDivModNames`, `boolTrueName`, `boolFalseName`) and asked
only for `StateOK`, so nothing made the handles `pinAt` hands back denote
anything and the conclusion was not provable.  Free at the one call site
(`Bridge/Checker/Arms.lean`'s `defn` arm, `hok4.check.pins`).

`sorry`: `natLitSupported` / `natOpDepsStored` / the `Bool`-family lookups
through `IFEnvOK`, then `natOpDeps_run`.  Task #97-P3-Checker's sorry list,
item 23. -/
theorem natOpGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.natOpGuard env2 nm := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpStoredOk) — the twin's list
recursion answers con-leche's `List.all` (DESIGN §3.4 forbids the closure).

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4): each step
is `natOpStoredOk`, which is `natOpTyPinned` on a hit, which reads the pin
table — so this walk is a pin reader too and `StateOK` alone was not enough.
Free at the one call site (`hok5.check.pins`).

`sorry`: a list induction over `natOpStoredOk`'s own `IFEnvOK` reads.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem natOpStoredOkAll_run {env2 : Env} {fe2 : IFEnv} {ds : List NIdx}
    {xs : List ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hd : denoteNL s.store ds xs)
    (hr : natOpStoredOkAll fe2 ds s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = xs.all (ConLeche.natOpStoredOk env2) := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpEquations) — the recurrence
equations, interned.

`sorry`: the pinned-literal constructions through the frontend tier's intern
exactness, as `Bridge/Checker/Basis.lean`'s item 15.  Task #97-P3-Checker's
sorry list, item 23. -/
theorem natOpEquations_run {d : Nat} {cn : NIdx} {nm : ConLeche.Name}
    {eqs : List (EIdx × EIdx)} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpEquations d cn s = .ok (eqs, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      EqPairsDenote s'.store eqs (ConLeche.natOpEquations d nm) := by
  sorry

/-- con-leche: ConLeche/Kernel/ExprOps.lean (Expr.substConst0) — the
self-reference substitution, pair by pair.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4):
`substConst0`'s `.const` arm reads `emptyLevels` and compares the stored
universe-argument handle against it, so without the pin invariant nothing
ties that comparison to con-leche's `us = []`.  Free at the one call site
(`hok7.check.pins`).

`sorry`: a list recursion over `Bridge/ExprOps/**`'s `substConst0` spec.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem substConst0Pairs_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx}
    {x : Expr} {eqs r : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store rh = some x) (hd : EqPairsDenote s.store eqs xs)
    (hr : substConst0Pairs cn rh eqs s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      EqPairsDenote s'.store r
        (xs.map fun eq => (Expr.substConst0 nm x eq.1,
          Expr.substConst0 nm x eq.2)) := by
  sorry



/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the
recurrence equations, certified by definitional equality in the pre-insertion
environment.

`sorry`: a list induction over `KnotSpec.defeq`, plus
`substConst0Pairs` and `natOpEquations`' exactness (both are pinned-term
constructions, so both are `Bridge/Checker/Basis.lean`'s shape).  Task
#97-P3-Checker's sorry list, item 23. -/
theorem certifyNatEqs_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {eqs : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {r : Bool} {s s' : AState} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s)
    (hden : EqPairsDenote s.store eqs xs)
    (hws : ∀ q ∈ xs, Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2)
    (hrun : certifyNatEqs μ fe eqs s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧
      (r = true → ∃ F, ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs
        = .ok true) := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the
substituted recurrence equations are well scoped at the depth the certifier
runs them at (`isDefEq … 2`: the equations' variables are `fvar 0` and
`fvar 1`).  A pure fact about con-leche's own pinned construction, which
`certifyNatEqs_bridge`'s `KnotSpec.defeq` calls need as their precondition.

`sorry`: `natOpEquations`' twelve literal shapes, and `Expr.substConst0`
preserving `WScoped` at a well-scoped replacement — which the stored value is,
by `EnvWF env2`'s own clause about a `defnInfo`'s value.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem natOpEqs_wscoped {env2 : Env} {nm : ConLeche.Name}
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (henv : EnvWF env2)
    (hf : env2.find? nm = some (.defnInfo cv' v' hint')) :
    ∀ q ∈ (ConLeche.natOpEquations 0 nm).map
      (fun eq => (Expr.substConst0 nm v' eq.1, Expr.substConst0 nm v' eq.2)),
      Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2 := by
  sorry

/-! ## The two pinned-variant gates -/

/-- con-leche: ConLeche/Kernel/Checker.lean:380-388 checkDivModPin — **the
`Nat.div`/`Nat.mod` variant gate**: the stored value must be definitionally
equal to some committed pin variant and that variant's certificates must
check.  No variant matching is a decline.

The loop is the one consumer of `Bridge/Checker/Base.lean`'s
`orElseAttempt_run`: each variant is an ATTEMPT, and a thrown error inside one
is "this variant does not match", recovered at the pre-attempt state.

`sorry`: `orElseAttempt_run` at each variant, `PinsDenote` to line the
variants up with con-leche's, `divModCertStmts`' pinned-term exactness, and
`KnotSpec.defeq` / `KnotSpec.infer` for the certificates.  Task
#97-P3-Checker's sorry list, item 24. -/
theorem checkDivModPin_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hok2 : StepOK env2 fe2 s)
    (hpins : PinsDenote s.store pins pinsP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : checkDivModPin μ pins fe fe2 cn s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
        = .ok () := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:407-425 checkReducePin — the
`Lean.reduceNat` / `Lean.reduceBool` install gate: the stored value must be
definitionally equal to the build-time pin.

`sorry`: `reduceStoredOk` / `reduceElemOk` / `reducePinGuard` through
`IFEnvOK`, then `KnotSpec.annotate` and `KnotSpec.defeq` at the
pinned term.  Task #97-P3-Checker's sorry list, item 24. -/
theorem checkReducePin_bridge {μ : CheckMode} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {value : EIdx}
    {x : Expr} {s s' : AState} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s)
    (hok2 : StepOK env2 fe2 s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store value = some x)
    (hrun : checkReducePin μ fe fe2 cn value s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
        = .ok () := by
  sorry

end ConRon.Bridge

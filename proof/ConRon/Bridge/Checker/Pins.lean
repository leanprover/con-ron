/-
# `ConRon.Bridge.Checker.Pins` — the startup walk, and what it leaves behind

`Arena/Checker.lean`'s `internAllPins` is DESIGN §8.6 P2d's one-time tree
walk, run by the driver before the prelude with the scratch tier CLOSED.  This
module is what it leaves behind, and the three clauses are exactly the three
the fold carries:

| | |
|---|---|
| `PinsOK s` | the forty-nine `PIN_*` slots denote `pinNames`, the reserved list denotes `reservedBasisNameValues`, the three nullary values denote, and **the zero name handle decodes to `.anonymous`** (`Bridge/StateOK.lean`; the last clause is task #97-P3-Ind round 5's, and this theorem is its debtor — see `PinsOK.anon`) |
| `PersPins s` | **every pin handle is persistent** — task #97-P3-0 §7's "one more clause", the one that makes `PinsOK` survive `dropScratch` (`Bridge/Checker/Inv.lean`'s `PinsOK.pmono`) |
| `PinsDenote s.store pins pinsP` | the interned `Nat`-operation pin variants denote con-leche's (`Bridge/Checker/Decl.lean`) |

`Arena/Pins.lean`'s own module note states the obligation:

> **Denotation unchanged.**  A pin is `internName` of the same `Name`, so the
> handle this record holds is the handle `pin` computed before […].  The one
> obligation the bridge owes is an instance of `intern_spec`:
> `pinsOK st → st.pins.names[PIN_NAT] = (internName st natName).1`

and `PinsOK` is the strengthened form of it: not that the handle is the one
`intern` would give, but that it DENOTES the right name, which is what every
consumer actually reads.

**Why the persistence clause is free.**  `internReservedPins` runs before the
parse, so `s.store.scratchOn = false` at the call; `intern`'s persistent
branch is the only one reachable, and every handle it produces has the
persistent tier bit.  The hypothesis below is therefore `s.store.scratchOn =
false` and nothing else.

**Why this module imports the frontend tier** (task #97-P3-Layout).
`internAllPins` interns whole `ConstantInfo`s, and the exactness of
`internCI` / `internCV` / `internExpr` is
`Bridge/Frontend/Shared.lean`'s — eighteen reads of it in the walk below.
That file used to sit ABOVE this one, because `Bridge/Frontend/Rel.lean`
imported `Bridge/Checker.lean` whole for three names that live in
`Bridge/Checker/Inv.lean`.  With that import narrowed, the frontend tier's
bottom is below the checker tier and this import is the right way round.
-/
import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.Checker.DeclVal

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
**the pin table, filled**: `internReservedPins` on a store with the scratch
tier closed leaves the table denoting and persistent.

`sorry`: `internNameList` over `Bridge/StoreNested.lean`'s
`EStore.internName` spec (49 + 19 interns), then `internLsNode` / `internLNode`
/ `internSortE` over `Bridge/Specs.lean`'s.  **`PinsOK.anon` is one more
obligation here** (task #97-P3-Ind round 5): every pin name is a `.str`/`.num`
chain bottoming out at `.anonymous`, so interning the first of them interns
`.anonymous` into the persistent `anons` table, whose only slot is 0 — and
`Idx.ofWord 0` is tag-`anonymous`, tier-persistent, slot 0.  The persistence half is the
`scratchOn = false` branch of `intern`, which `Arena/WFProofs.lean`'s
`intern_view_spec` already exposes.  Task #97-P3-Checker's sorry list,
item 13. -/
theorem internReservedPins_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    (hrun : internReservedPins s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      s'.store.scratchOn = false ∧ s'.memos = s.memos ∧ s'.caches = s.caches := by
  sorry

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — **the pin variants,
interned**: `internPinSets` on a closed scratch tier hands back a list that
denotes its argument, variant by variant, in persistent handles.

`sorry`: sixteen `Frontend.internExpr` calls per variant, over the frontend
tier's intern exactness (`denoteE (internExpr e) = some e`), and the list
recursion.  Task #97-P3-Checker's sorry list, item 13. -/
theorem internPinSets_run {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hrun : internPinSets ps s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsDenote s'.store r ps ∧
      PersPinSets r ∧ s'.store.scratchOn = false ∧ s'.pins = s.pins ∧
      s'.caches = s.caches ∧ s'.memos = s.memos := by
  sorry

/-- con-leche: ConLeche/Kernel/Basis.lean:41-66 BasisKind.decls — the raw
pinned block's intern, as one scratch-agnostic step. -/
theorem BasisKind.decls_sstep {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s) (hrun : BasisKind.decls k s = .ok (r, s')) :
    Frontend.IStepS s s' := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst
  exact (Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
    (Frontend.EMemoOK.empty s.store) hgo).1

/-- con-leche: ConLeche/Kernel/BasisA.lean:51-57 BasisKind.declsA — the
annotated pinned block's intern, as one scratch-agnostic step. -/
theorem BasisKind.declsA_sstep {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.declsA k s = .ok (r, s')) : Frontend.IStepS s s' := by
  simp only [ConRon.Arena.BasisKind.declsA, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst
  exact (Frontend.internCIList_sstep (ConLeche.BasisKind.declsA k) hok
    (Frontend.EMemoOK.empty s.store) hgo).1

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:72-73 reduceOpNames — two pin
reads; the state is left alone. -/
theorem reduceOpNames_state {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : reduceOpNames s = .ok (ns, s')) : s' = s := by
  simp only [Arena.reduceOpNames] at hr
  obtain ⟨a, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, -⟩ := pinAt_run (x := ConLeche.reduceNatName) hp rfl q0
  rw [p0] at w0
  obtain ⟨b, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨p1, -⟩ := pinAt_run (x := ConLeche.reduceBoolName) hp rfl q1
  rw [p1] at w1
  exact (AM.pure_ok w1).2

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the same walk as `reservedBasisNames_run`, in the scratch-agnostic frame: six
pin reads leave the state alone and thirteen `internName`s are `IStepS`
steps.  The startup walk needs the `scratchOn` equation `PinStep` does not
carry. -/
theorem reservedBasisNames_sstep {s s' : AState} {hs : List NIdx}
    (hst : StateOK s) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) : Frontend.IStepS s s' := by
  simp only [Arena.reservedBasisNames] at hr
  have a0 : Frontend.IStepS s s := Frontend.IStepS.refl hst
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, -⟩ := pinAt_run (x := ConLeche.eqName) (hp.mono a0.ext a0.pins) rfl q0
  rw [p0] at w0
  have a1 := a0
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a1.trans (Frontend.internName_sstep a1.ok q1).1
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (Frontend.internName_sstep a2.ok q2).1
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  obtain ⟨p3, -⟩ := pinAt_run (x := ConLeche.natName) (hp.mono a3.ext a3.pins) rfl q3
  rw [p3] at w3
  have a4 := a3
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  obtain ⟨p4, -⟩ := pinAt_run (x := ConLeche.natZeroName) (hp.mono a4.ext a4.pins) rfl q4
  rw [p4] at w4
  have a5 := a4
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  obtain ⟨p5, -⟩ := pinAt_run (x := ConLeche.natSuccName) (hp.mono a5.ext a5.pins) rfl q5
  rw [p5] at w5
  have a6 := a5
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  have a7 := a6.trans (Frontend.internName_sstep a6.ok q6).1
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  obtain ⟨p7, -⟩ := pinAt_run (x := ConLeche.punitName) (hp.mono a7.ext a7.pins) rfl q7
  rw [p7] at w7
  have a8 := a7
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  have a9 := a8.trans (Frontend.internName_sstep a8.ok q8).1
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  have a10 := a9.trans (Frontend.internName_sstep a9.ok q9).1
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  have a11 := a10.trans (Frontend.internName_sstep a10.ok q10).1
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  have a12 := a11.trans (Frontend.internName_sstep a11.ok q11).1
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  have a13 := a12.trans (Frontend.internName_sstep a12.ok q12).1
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  have a14 := a13.trans (Frontend.internName_sstep a13.ok q13).1
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  have a15 := a14.trans (Frontend.internName_sstep a14.ok q14).1
  obtain ⟨_, u15, q15, w15⟩ := AM.bind_ok w14
  have a16 := a15.trans (Frontend.internName_sstep a15.ok q15).1
  obtain ⟨_, u16, q16, w16⟩ := AM.bind_ok w15
  have a17 := a16.trans (Frontend.internName_sstep a16.ok q16).1
  obtain ⟨_, u17, q17, w17⟩ := AM.bind_ok w16
  have a18 := a17.trans (Frontend.internName_sstep a17.ok q17).1
  obtain ⟨_, u18, q18, w18⟩ := AM.bind_ok w17
  obtain ⟨p18, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hp.mono a18.ext a18.pins) rfl q18
  rw [p18] at w18
  have a19 := a18
  obtain ⟨-, rfl⟩ := AM.pure_ok w18
  exact a19

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
**THE STARTUP WALK**: `internAllPins` interns every datum the checker compares
a stream record against, and hands back the interned pin list.  Its
postcondition is the fold's precondition — `PinsOK`, `PersPins`,
`PinsDenote`, `PersPinSets` — which is why the capstone
(`Bridge/Checker/Capstone.lean`) can take those four as hypotheses and the
driver tier can discharge all four here.

**`internAllPins` does NOT establish `PinsOK`** — `internReservedPins` does,
and the driver runs it first (`Arena/Main.lean`).  So `PinsOK` and `PersPins`
are hypotheses here and travel through: the walk only appends, and
`PinsOK.mono` carries them.

**The per-call frame** (asked for by the Frontend tier, task
#97-P3-Checker-2): the walk touches the four stores and the pin record and
NOTHING else, so `s'.caches = s.caches` and `s'.memos = s.memos` come out
with the rest.  `Bridge/Frontend/Capstone.lean`'s
`no_False_declaration_pipeline` needs them for the `internAllPins` call
`runPipelineM` makes between `preparePrelude` and `installThenCheck`.

**PROVED** (task #97-P3-Checker round 8), relative to `internPinSets_run`:
thirty-six links, each a scratch-agnostic `IStepS` — the twelve basis blocks
(`BasisKind.decls_sstep` / `declsA_sstep`), eighteen fresh-memo interns
(`internCI_fresh`, `internCV_fresh`, `Frontend.internExpr_sstep`),
`reservedBasisNames_sstep`, and six pin reads that leave the state alone —
then `internPinSets_run` for the variants.  `PersPins` travels because the pin
record is untouched and persistence is a fact about handles. -/
theorem internAllPins_run {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s)
    (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      PinsDenote s'.store r ps ∧ PersPinSets r ∧
      s'.store.scratchOn = false ∧
      s'.caches = s.caches ∧ s'.memos = s.memos := by
  simp only [Arena.internAllPins] at hrun
  have a0 : Frontend.IStepS s s := Frontend.IStepS.refl hok
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hrun
  have a1 := a0.trans (BasisKind.decls_sstep a0.ok q0)
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a1.trans (BasisKind.declsA_sstep a1.ok q1)
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (BasisKind.decls_sstep a2.ok q2)
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  have a4 := a3.trans (BasisKind.declsA_sstep a3.ok q3)
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  have a5 := a4.trans (BasisKind.decls_sstep a4.ok q4)
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  have a6 := a5.trans (BasisKind.declsA_sstep a5.ok q5)
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  have a7 := a6.trans (BasisKind.decls_sstep a6.ok q6)
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  have a8 := a7.trans (BasisKind.declsA_sstep a7.ok q7)
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  have a9 := a8.trans (BasisKind.decls_sstep a8.ok q8)
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  have a10 := a9.trans (BasisKind.declsA_sstep a9.ok q9)
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  have a11 := a10.trans (BasisKind.decls_sstep a10.ok q10)
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  have a12 := a11.trans (BasisKind.declsA_sstep a11.ok q11)
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  have a13 := a12.trans (internCI_fresh a12.ok q12).1
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  have a14 := a13.trans (internCI_fresh a13.ok q13).1
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  have a15 := a14.trans (internCI_fresh a14.ok q14).1
  obtain ⟨_, u15, q15, w15⟩ := AM.bind_ok w14
  have a16 := a15.trans (internCI_fresh a15.ok q15).1
  obtain ⟨_, u16, q16, w16⟩ := AM.bind_ok w15
  have a17 := a16.trans (internCI_fresh a16.ok q16).1
  obtain ⟨_, u17, q17, w17⟩ := AM.bind_ok w16
  have a18 := a17.trans (internCI_fresh a17.ok q17).1
  obtain ⟨_, u18, q18, w18⟩ := AM.bind_ok w17
  have a19 := a18.trans (internCV_fresh a18.ok q18).1
  obtain ⟨_, u19, q19, w19⟩ := AM.bind_ok w18
  have a20 := a19.trans (internCV_fresh a19.ok q19).1
  obtain ⟨_, u20, q20, w20⟩ := AM.bind_ok w19
  have a21 := a20.trans (internCV_fresh a20.ok q20).1
  obtain ⟨_, u21, q21, w21⟩ := AM.bind_ok w20
  have a22 := a21.trans (internCV_fresh a21.ok q21).1
  obtain ⟨_, u22, q22, w22⟩ := AM.bind_ok w21
  have a23 := a22.trans (internCV_fresh a22.ok q22).1
  obtain ⟨_, u23, q23, w23⟩ := AM.bind_ok w22
  have a24 := a23.trans (internCV_fresh a23.ok q23).1
  obtain ⟨_, u24, q24, w24⟩ := AM.bind_ok w23
  have a25 := a24.trans (internCV_fresh a24.ok q24).1
  obtain ⟨_, u25, q25, w25⟩ := AM.bind_ok w24
  have a26 := a25.trans (internCV_fresh a25.ok q25).1
  obtain ⟨_, u26, q26, w26⟩ := AM.bind_ok w25
  have a27 := a26.trans (internCV_fresh a26.ok q26).1
  obtain ⟨_, u27, q27, w27⟩ := AM.bind_ok w26
  have a28 := a27.trans (internCV_fresh a27.ok q27).1
  obtain ⟨_, u28, q28, w28⟩ := AM.bind_ok w27
  have a29 := a28.trans (Frontend.internExpr_sstep a28.ok q28).1
  obtain ⟨_, u29, q29, w29⟩ := AM.bind_ok w28
  have a30 := a29.trans (Frontend.internExpr_sstep a29.ok q29).1
  obtain ⟨_, u30, q30, w30⟩ := AM.bind_ok w29
  have a31 := a30.trans (reservedBasisNames_sstep a30.ok (hpins.mono a30.ext a30.pins) q30)
  obtain ⟨_, u31, q31, w31⟩ := AM.bind_ok w30
  obtain ⟨rfl, -⟩ := natOpNames_run (hpins.mono a31.ext a31.pins) q31
  have a32 := a31
  obtain ⟨_, u32, q32, w32⟩ := AM.bind_ok w31
  obtain ⟨rfl, -⟩ := natDivModNames_run (hpins.mono a32.ext a32.pins) q32
  have a33 := a32
  obtain ⟨_, u33, q33, w33⟩ := AM.bind_ok w32
  obtain rfl := reduceOpNames_state (hpins.mono a33.ext a33.pins) q33
  have a34 := a33
  obtain ⟨_, u34, q34, w34⟩ := AM.bind_ok w33
  obtain ⟨p34, -⟩ := pinAt_run (x := ConLeche.sorryAxName) (hpins.mono a34.ext a34.pins) rfl q34
  rw [p34] at w34
  have a35 := a34
  obtain ⟨_, u35, q35, w35⟩ := AM.bind_ok w34
  obtain ⟨p35, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hpins.mono a35.ext a35.pins) rfl q35
  rw [p35] at w35
  have a36 := a35
  obtain ⟨hst', hx', hden, hpps, hoff', hpe, hce, hme⟩ :=
    internPinSets_run a36.ok (by rw [a36.scratch]; exact hoff) w35
  have hpeq : s'.pins = s.pins := by rw [hpe, a36.pins]
  refine ⟨hst', a36.ext.trans hx', hpins.mono (a36.ext.trans hx') hpeq, ?_, hden,
    hpps, hoff', by rw [hce, a36.caches], by rw [hme, a36.memos]⟩
  exact ⟨by rw [hpeq]; exact hpp.names, by rw [hpeq]; exact hpp.reserved,
    by rw [hpeq]; exact hpp.emptyLevels, by rw [hpeq]; exact hpp.zeroLevel,
    by rw [hpeq]; exact hpp.sortOne⟩

end ConRon.Bridge

/-
# `ConRon.Bridge.Checker.NatOpNames` — the structural-`Nat` operations' names, off the pin table

`natOpNames`, `natDivModNames` and `natOpDeps` read the pin table and nothing else, so their run
forms need only the pins (`PinsOK`) and the name tier: they are read by the value checks
(`Bridge/Checker/DeclVal.lean`) and by the preparation's ground hoist
(`Bridge/Frontend/Prepare.lean`).
-/
module

import ConRon.Bridge.Specs
public import ConRon.Bridge.Checker.Names
public import ConRon.Bridge.Checker.Inv

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:475-481 natOpNames — the seven
structural fast-path operations, off the pin table.

The proof: seven `pinAt_run`s, in
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

The proof is `natOpNames_run`'s, one slot longer. -/
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

The proof: fifteen `pinAt_run`s, `beq_handle_iff` at
each of the fifteen tests, and the sixteen arms.  A pin read leaves the state
alone, so every arm's frame is the same `rfl`-shaped record and the only
content is which list comes out.

**Why `PinsOK s`**: it reads the pin table fifteen times, and without it
nothing makes the handles `pinAt` hands back denote anything.  It is free at
the one call site
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
  · exact frame _ a0 (by simp only [ConLeche.natOpDeps, ite_eq_left (b0.mp y0)]; exact ⟨d0, trivial⟩)
  have nb0 : ¬ (nm = ConLeche.natPredName) := fun h => z0 (b0.mpr h)
  rcases AM.ite_ok v0 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · exact frame _ a1 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_left (b1.mp y1)]; exact ⟨d1, trivial⟩)
  have nb1 : ¬ (nm = ConLeche.natAddName) := fun h => z1 (b1.mpr h)
  rcases AM.ite_ok v1 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · exact frame _ a2 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_left (b2.mp y2)]; exact ⟨d0, d2, trivial⟩)
  have nb2 : ¬ (nm = ConLeche.natSubName) := fun h => z2 (b2.mpr h)
  rcases AM.ite_ok v2 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · exact frame _ a3 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_left (b3.mp y3)]; exact ⟨d1, d3, trivial⟩)
  have nb3 : ¬ (nm = ConLeche.natMulName) := fun h => z3 (b3.mpr h)
  rcases AM.ite_ok v3 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · exact frame _ a4 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_left (b4.mp y4)]; exact ⟨d1, d3, d4, trivial⟩)
  have nb4 : ¬ (nm = ConLeche.natPowName) := fun h => z4 (b4.mpr h)
  rcases AM.ite_ok v4 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · exact frame _ a5 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_left (b5.mp y5)]; exact ⟨d5, trivial⟩)
  have nb5 : ¬ (nm = ConLeche.natBeqName) := fun h => z5 (b5.mpr h)
  rcases AM.ite_ok v5 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · exact frame _ a6 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_left (b6.mp y6)]; exact ⟨d6, trivial⟩)
  have nb6 : ¬ (nm = ConLeche.natBleName) := fun h => z6 (b6.mpr h)
  rcases AM.ite_ok v6 with ⟨y7, a7⟩ | ⟨z7, v7⟩
  · exact frame _ a7 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_left (b7.mp y7)]; exact ⟨d0, d2, d6, d7, trivial⟩)
  have nb7 : ¬ (nm = ConLeche.natDivName) := fun h => z7 (b7.mpr h)
  rcases AM.ite_ok v7 with ⟨y8, a8⟩ | ⟨z8, v8⟩
  · exact frame _ a8 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_left (b8.mp y8)]; exact ⟨d0, d2, d6, d8, trivial⟩)
  have nb8 : ¬ (nm = ConLeche.natModName) := fun h => z8 (b8.mpr h)
  rcases AM.ite_ok v8 with ⟨y9, a9⟩ | ⟨z9, v9⟩
  · exact frame _ a9 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_left (b9.mp y9)]; exact ⟨d6, d8, d9, trivial⟩)
  have nb9 : ¬ (nm = ConLeche.natGcdName) := fun h => z9 (b9.mpr h)
  rcases AM.ite_ok v9 with ⟨y10, a10⟩ | ⟨z10, v10⟩
  · exact frame _ a10 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_left (b10.mp y10)]; exact ⟨d1, d3, d6, d7, d8, d10, trivial⟩)
  have nb10 : ¬ (nm = ConLeche.natLandName) := fun h => z10 (b10.mpr h)
  rcases AM.ite_ok v10 with ⟨y11, a11⟩ | ⟨z11, v11⟩
  · exact frame _ a11 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_right nb10, ite_eq_left (b11.mp y11)]; exact ⟨d1, d2, d3, d6, d7, d8, d11, trivial⟩)
  have nb11 : ¬ (nm = ConLeche.natLorName) := fun h => z11 (b11.mpr h)
  rcases AM.ite_ok v11 with ⟨y12, a12⟩ | ⟨z12, v12⟩
  · exact frame _ a12 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_right nb10, ite_eq_right nb11, ite_eq_left (b12.mp y12)]; exact ⟨d1, d3, d6, d7, d8, d12, trivial⟩)
  have nb12 : ¬ (nm = ConLeche.natXorName) := fun h => z12 (b12.mpr h)
  rcases AM.ite_ok v12 with ⟨y13, a13⟩ | ⟨z13, v13⟩
  · exact frame _ a13 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_right nb10, ite_eq_right nb11, ite_eq_right nb12, ite_eq_left (b13.mp y13)]; exact ⟨d2, d3, d6, d13, trivial⟩)
  have nb13 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z13 (b13.mpr h)
  rcases AM.ite_ok v13 with ⟨y14, a14⟩ | ⟨z14, v14⟩
  · exact frame _ a14 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_right nb10, ite_eq_right nb11, ite_eq_right nb12, ite_eq_right nb13, ite_eq_left (b14.mp y14)]; exact ⟨d2, d6, d7, d14, trivial⟩)
  have nb14 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z14 (b14.mpr h)
  exact frame _ v14 (by simp only [ConLeche.natOpDeps, ite_eq_right nb0, ite_eq_right nb1, ite_eq_right nb2, ite_eq_right nb3, ite_eq_right nb4, ite_eq_right nb5, ite_eq_right nb6, ite_eq_right nb7, ite_eq_right nb8, ite_eq_right nb9, ite_eq_right nb10, ite_eq_right nb11, ite_eq_right nb12, ite_eq_right nb13, ite_eq_right nb14]; exact trivial)

end ConRon.Bridge

/-
# `ConRon.Bridge.Inductives.StructParts` — Theorem 1 for the generators

`Arena/Inductives/StructParts.lean`'s twenty-nine twins against
`ConLeche/Kernel/Inductives/StructParts.lean`: the families, the spines, the
Π→λ rewrites, the structure recogniser, the projection bodies and the two
memoised `Expr` predicates.

**Every twin here is PURE grade.**  Not one of them calls the knot: they
intern nodes, read the store, read the pin table and walk handles.  So every
statement is a `PSpec` and the frame is `PStep` — task #97-P3-0 §2's rule that
an `ExprOps`-shaped theorem must not carry the cache clauses, applied to the
generators.

## The three memo invariants

`hasLooseBVarBGo`, `structUsedLaterGo` and `mentionsConstGo` thread an
explicit `Std.HashMap` (task #97d-2's deviation 5: the memo stays an ARGUMENT
because each answer depends on data fixed for one call, and nothing was added
to `AState`).  Each needs an invariant in `Bridge/StateOK.lean`'s `MemoOK`
shape — "every recorded answer is the real one" — and the invariant travels
in and out of the walk, which is what makes these three statements different
from the other twenty-six.

con-leche's own are `LooseBVarMemoInv` (`StructParts.lean:428-433`) and
`MentionsMemoInv` (`StructParts.lean:806-812`); the arena's are the same
predicate at handle keys, through `denoteE`.
-/
import ConRon.Bridge.Inductives.Rel

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The three memo invariants -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:428-433 LooseBVarMemoInv
The `(handle, cursor)`-keyed memo of `hasLooseBVarB`: every recorded answer is
the real one at the key's own cursor. -/
def LooseMemoOK (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ r = Expr.hasLooseBVarB k.2 e

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:806-812 MentionsMemoInv
The handle-keyed memo of `mentionsConst T`. -/
def MentionsMemoOK (T : ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsConst T e

/-- con-leche: none — the empty memo is sound. -/
theorem LooseMemoOK.empty {st : EStore} : LooseMemoOK ∅ st := by
  intro k r h; simp at h

/-- con-leche: none — the invariant is about DENOTATIONS, so it survives an
arena extension: the tier's memos travel through interning walks. -/
theorem LooseMemoOK.mono {tbl : Std.HashMap (EIdx × Nat) Bool}
    {st st' : EStore} (hm : LooseMemoOK tbl st) (hx : Ext st st') :
    LooseMemoOK tbl st' := by
  intro k r hk
  obtain ⟨e, he, hr⟩ := hm k r hk
  exact ⟨e, denote_ext he hx, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:435-440
LooseBVarMemoInv.insert — recording a TRUE answer keeps the memo sound.  This
is `Arena.hasLooseBVarBIns` read as an invariant step. -/
theorem LooseMemoOK.insert {tbl : Std.HashMap (EIdx × Nat) Bool} {st : EStore}
    (hm : LooseMemoOK tbl st) {h : EIdx} {i : Nat} {hP : Expr} {r : Bool}
    (hd : denoteE st h = some hP) (heq : r = Expr.hasLooseBVarB i hP) :
    LooseMemoOK (tbl.insert (h, i) r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-- con-leche: none — the empty `mentionsConst` memo is sound. -/
theorem MentionsMemoOK.empty {T : ConLeche.Name} {st : EStore} :
    MentionsMemoOK T ∅ st := by
  intro k r h; simp at h

/-- con-leche: none — and it survives an arena extension. -/
theorem MentionsMemoOK.mono {T : ConLeche.Name} {tbl : Std.HashMap EIdx Bool}
    {st st' : EStore} (hm : MentionsMemoOK T tbl st) (hx : Ext st st') :
    MentionsMemoOK T tbl st' := by
  intro k r hk
  obtain ⟨e, he, hr⟩ := hm k r hk
  exact ⟨e, denote_ext he hx, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:806-812
MentionsMemoInv.insert — the same invariant step for the name walk. -/
theorem MentionsMemoOK.insert {T : ConLeche.Name}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} (hm : MentionsMemoOK T tbl st)
    {h : EIdx} {hP : Expr} {r : Bool} (hd : denoteE st h = some hP)
    (heq : r = Expr.mentionsConst T hP) :
    MentionsMemoOK T (tbl.insert h r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-! ## Level lists over handles -/

/-- con-leche: none — `lps.map .param`, interned.  con-leche writes the list
inline at every use; over handles a level list is a node, so the twin builds
it once and this is the one statement that says the node is that list.

**CLOSED** (task #97-P3-Ind round 2): the `let rec go` by list induction over
`internParamL_run`, then `internLsNode_run` at the result.  Both run forms are
`Bridge/Inductives/Rel.lean`'s, which is where this tier's `AM.of_run`
boilerplate lives. -/
theorem paramLevels_go_run : ∀ (lps : List NIdx) {lpsP : List ConLeche.Name}
    {s s' : AState} {r : List LIdx}, StateOK s →
    Frontend.denoteNList s.store.ns lps = some lpsP →
    Arena.paramLevels.go lps s = .ok (r, s') →
    PStep s s' ∧ denoteLList s'.store.ls r = some (lpsP.map Level.param) := by
  intro lps
  induction lps with
  | nil =>
    intro lpsP s s' r hok hd hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.paramLevels.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons n ns ih =>
    intro lpsP s s' r hok hd hrun
    simp only [Frontend.denoteNList] at hd
    cases hn : denoteN s.store.ns n with
    | none => rw [hn] at hd; simp at hd
    | some x =>
      cases hns : Frontend.denoteNList s.store.ns ns with
      | none => rw [hn, hns] at hd; simp at hd
      | some xs =>
        rw [hn, hns] at hd
        obtain rfl := Option.some.inj hd
        simp only [Arena.paramLevels.go] at hrun
        obtain ⟨u, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨rest, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨hstep1, hu⟩ := internParamL_run hok hn h1
        obtain ⟨hstep2, hrest⟩ :=
          ih hstep1.ok (denoteNListE_ext hstep1.ext _ _ hns) h3
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨hstep1.trans hstep2, ?_⟩
        simp only [denoteLList, opt2, denoteL_ext hu hstep2.ext, hrest,
          List.map_cons]

theorem paramLevels_spec (lps : List NIdx) (lpsP : List ConLeche.Name) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.paramLevels lps) (RLs (lpsP.map Level.param)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.paramLevels] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hus⟩ := paramLevels_go_run lps hok hd h1
  obtain ⟨hstep2, hr⟩ := internLsNode_run hstep1.ok hus h2
  exact ⟨hstep1.trans hstep2, hr⟩

/-! ## The families and the spines -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
The parameter variables as seen from under `o` extra binders.

**CLOSED** (task #97-P3-Ind round 2): a `Nat` recursion over
`internBVarE_run` with the cursor `k` generalised.  The pure side is a
`List.range` map, so the step is `List.range_succ_eq_map` and one `omega` on
the index arithmetic (`k + (j + 1) = k + 1 + j`). -/
theorem structPsAt_go_run (o nP : Nat) : ∀ (n k : Nat) {s s' : AState}
    {r : List EIdx}, StateOK s → Arena.structPsAt.go o nP n k s = .ok (r, s') →
    PStep s s' ∧ Frontend.denoteEList s'.store r
      = some ((List.range n).map fun j => Expr.bvar (o + nP - 1 - (k + j))) := by
  intro n
  induction n with
  | zero =>
    intro k s s' r hok hrun
    simp only [Arena.structPsAt.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | succ n ih =>
    intro k s s' r hok hrun
    simp only [Arena.structPsAt.go] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨rest, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨hstep1, hb⟩ := internBVarE_run hok h1
    obtain ⟨hstep2, hrest⟩ := ih (k + 1) hstep1.ok h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨hstep1.trans hstep2, ?_⟩
    have hkey : ((List.range (n + 1)).map fun j => Expr.bvar (o + nP - 1 - (k + j)))
        = Expr.bvar (o + nP - 1 - k) ::
          ((List.range n).map fun j => Expr.bvar (o + nP - 1 - (k + 1 + j))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left (fun j _ => ?_)
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hkey]
    simp only [Frontend.denoteEList, denote_ext hb hstep2.ext, hrest]

theorem structPsAt_spec (o nP : Nat) :
    PSpec PT (Arena.structPsAt o nP) (REL (ConLeche.structPsAt o nP)) := by
  intro s₀ s' r hok _ hrun
  obtain ⟨hstep, hd⟩ := structPsAt_go_run o nP nP 0 hok hrun
  refine ⟨hstep, ?_⟩
  simpa only [ConLeche.structPsAt, Nat.zero_add] using hd

/-- con-leche: none — `bvarsDesc n` is `structPsAt 0 n`, `rfl` on both sides. -/
theorem bvarsDesc_spec (n : Nat) :
    PSpec PT (Arena.bvarsDesc n) (REL (ConLeche.structPsAt 0 n)) :=
  structPsAt_spec 0 n

/-- con-leche: none — two `bvar` spines over the same range agree as soon as
their index arithmetic does.  The four spine generators below differ from
con-leche's only in how the offset is spelled (`structPsAt (nF + 1) nP`
against `fun i => bvar (nF + nP - i)`, `structPsAt 0 nF` against `fun j =>
bvar (nF - 1 - j)`), and this plus `omega` is the whole of that difference. -/
theorem bvarRange_congr {n : Nat} {f g : Nat → Nat} (h : ∀ j, f j = g j) :
    ((List.range n).map fun j => Expr.bvar (f j))
      = (List.range n).map fun j => Expr.bvar (g j) :=
  List.map_congr_left (fun j _ => by rw [h j])

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:82-86 structFam
The type former applied to its parameter variables.

**CLOSED** (task #97-P3-Ind round 2): `paramLevels_spec`, `internConstE_run`,
`structPsAt_spec` and `mkAppN_run`, composed by three `bindOk`s. -/
theorem structFam_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP o : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structFam T lps nP o) (RE (ConLeche.structFam TP lpsP nP o)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps⟩ := hpre
  simp only [Arena.structFam] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hus⟩ := paramLevels_spec lps lpsP s₀ s₁ us hok hlps h1
  obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hhd⟩ :=
    internConstE_run hstep1.ok (denoteN_ext hT hstep1.ext) hus h3
  obtain ⟨ps, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hps⟩ := structPsAt_spec o nP s₂ s₃ ps hstep2.ok trivial h5
  obtain ⟨hstep4, hr⟩ :=
    mkAppN_run ps _ hstep3.ok (denote_ext hhd hstep3.ext) hps h6
  refine ⟨hstep1.trans (hstep2.trans (hstep3.trans hstep4)), ?_⟩
  simpa only [ConLeche.structFam, ConLeche.structPsAt] using hr

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
The constructor applied to the parameter and field variables.

**CLOSED** (task #97-P3-Ind round 2): `structFam_spec`'s composition with the
two spines appended (`denoteEList_append`), and `bvarRange_congr` for the two
places con-leche spells the offset differently — `structPsAt (nF + 1) nP`
against `fun i => bvar (nF + nP - i)`, `structPsAt 0 nF` against `fun j =>
bvar (nF - 1 - j)`.  Both are `omega`. -/
theorem structCtorSpine_spec (C : NIdx) (CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structCtorSpine C lps nP nF)
      (RE (ConLeche.structCtorSpine CP lpsP nP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hC, hlps⟩ := hpre
  simp only [Arena.structCtorSpine] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hus⟩ := paramLevels_spec lps lpsP s₀ s₁ us hok hlps h1
  obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hhd⟩ :=
    internConstE_run hstep1.ok (denoteN_ext hC hstep1.ext) hus h3
  obtain ⟨ps, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hps⟩ :=
    structPsAt_spec (nF + 1) nP s₂ s₃ ps hstep2.ok trivial h5
  obtain ⟨fs, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨hstep4, hfs⟩ := bvarsDesc_spec nF s₃ s₄ fs hstep3.ok trivial h7
  obtain ⟨hstep5, hr⟩ :=
    mkAppN_run (ps ++ fs) _ hstep4.ok
      (denote_ext hhd (hstep3.ext.trans hstep4.ext))
      (denoteEList_append (denoteEList_ext hstep4.ext _ _ hps) hfs) h8
  refine ⟨hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5))), ?_⟩
  have hargs : ((List.range nP).map fun i => Expr.bvar (nF + nP - i)) ++
        ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))
      = ConLeche.structPsAt (nF + 1) nP ++ ConLeche.structPsAt 0 nF := by
    simp only [ConLeche.structPsAt]
    rw [bvarRange_congr (n := nP) (f := fun i => nF + nP - i)
          (g := fun k => nF + 1 + nP - 1 - k) (fun j => by omega),
        bvarRange_congr (n := nF) (f := fun j => nF - 1 - j)
          (g := fun k => 0 + nF - 1 - k) (fun j => by omega)]
  rw [ConLeche.structCtorSpine, hargs]
  exact hr

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:96-99 structRuleBody
The minor premise applied to the field variables.

**CLOSED** (task #97-P3-Ind round 2): `internBVarE_run`, `bvarsDesc_spec` and
`mkAppN_run`. -/
theorem structRuleBody_spec (nF : Nat) :
    PSpec PT (Arena.structRuleBody nF) (RE (ConLeche.structRuleBody nF)) := by
  intro s₀ s' r hok _ hrun
  simp only [Arena.structRuleBody] at hrun
  obtain ⟨hd, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hhd⟩ := internBVarE_run hok h1
  obtain ⟨fs, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hfs⟩ := bvarsDesc_spec nF s₁ s₂ fs hstep1.ok trivial h3
  obtain ⟨hstep3, hr⟩ :=
    mkAppN_run fs _ hstep2.ok (denote_ext hhd hstep2.ext) hfs h4
  refine ⟨hstep1.trans (hstep2.trans hstep3), ?_⟩
  have hargs : ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))
      = ConLeche.structPsAt 0 nF := by
    simp only [ConLeche.structPsAt]
    exact bvarRange_congr (fun j => by omega)
  rw [ConLeche.structRuleBody, hargs]
  exact hr

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:139-142 structElimLevel
The recursor's elimination level.

**CLOSED** (task #97-P3-Ind round 2): `internParamL_run` / `internZeroL_run`
under one `cases` on the eliminator bit. -/
theorem structElimLevel_spec (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) :
    PSpec (fun st => denoteN st.ns elim = some elimP)
      (Arena.structElimLevel elim large)
      (RL (ConLeche.structElimLevel elimP large)) := by
  intro s₀ s' r hok hd hrun
  cases large with
  | true =>
    simp only [Arena.structElimLevel, if_true] at hrun
    obtain ⟨hstep, hr⟩ := internParamL_run hok hd hrun
    exact ⟨hstep, by simpa only [ConLeche.structElimLevel, if_true] using hr⟩
  | false =>
    simp only [Arena.structElimLevel, Bool.false_eq_true, if_false] at hrun
    obtain ⟨hstep, hr⟩ := internZeroL_run hok hrun
    exact ⟨hstep, by
      simpa only [ConLeche.structElimLevel, Bool.false_eq_true, if_false]
        using hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:144-150 structCtorSpineAt
`structCtorSpine` at an arbitrary offset between the parameters and the
fields.

**CLOSED** (task #97-P3-Ind round 2): `structCtorSpine_spec`'s proof at the
offset `o + nF`; con-leche spells its first spine as `structPsAt (o + nF) nP`
here, so only the field spine needs `bvarRange_congr`. -/
theorem structCtorSpineAt_spec (C : NIdx) (CP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (o nP nF : Nat) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structCtorSpineAt C lps o nP nF)
      (RE (ConLeche.structCtorSpineAt CP lpsP o nP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hC, hlps⟩ := hpre
  simp only [Arena.structCtorSpineAt] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hus⟩ := paramLevels_spec lps lpsP s₀ s₁ us hok hlps h1
  obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hhd⟩ :=
    internConstE_run hstep1.ok (denoteN_ext hC hstep1.ext) hus h3
  obtain ⟨ps, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hps⟩ :=
    structPsAt_spec (o + nF) nP s₂ s₃ ps hstep2.ok trivial h5
  obtain ⟨fs, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨hstep4, hfs⟩ := bvarsDesc_spec nF s₃ s₄ fs hstep3.ok trivial h7
  obtain ⟨hstep5, hr⟩ :=
    mkAppN_run (ps ++ fs) _ hstep4.ok
      (denote_ext hhd (hstep3.ext.trans hstep4.ext))
      (denoteEList_append (denoteEList_ext hstep4.ext _ _ hps) hfs) h8
  refine ⟨hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5))), ?_⟩
  have hargs : ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))
      = ConLeche.structPsAt 0 nF := by
    simp only [ConLeche.structPsAt]
    exact bvarRange_congr (fun j => by omega)
  rw [ConLeche.structCtorSpineAt, hargs]
  exact hr

/-! ## The Π→Π and Π→λ rewrites -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:152-158 Expr.replacePisPw
Replace a `k`-binder Π-telescope's body, re-stamping every binder's `PropWhen`.

**CLOSED** (task #97-P3-Ind round 2): a `Nat` recursion whose binder arm is
`internForallEE_run` (the binder datum is a VALUE here, not a handle, so this
is the plain `internE` face and not task #97-P6-16's).  The eight arms that
are not a binder answer `none` on BOTH sides, which is the two-sidedness
`ROp` asks for — a handle's view and its denotation have the same
constructor. -/
theorem replacePisPw_spec (pw : PropWhen) (k : Nat) : ∀ (h b : EIdx)
    (hP bP : Expr),
    PSpec (fun st => denoteE st h = some hP ∧ denoteE st b = some bP)
      (Arena.replacePisPw pw k h b)
      (ROp RE (Expr.replacePisPw pw k hP bP)) := by
  induction k with
  | zero =>
    intro h b hP bP s₀ s' r hok hpre hrun
    obtain ⟨_, hb⟩ := hpre
    simp only [Arena.replacePisPw] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, bP, rfl, hb⟩
  | succ k ih =>
    intro h b hP bP s₀ s' r hok hpre hrun
    obtain ⟨hh, hb⟩ := hpre
    simp only [Arena.replacePisPw] at hrun
    obtain ⟨v, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hs1, hw⟩ := view_run h1
    rw [hs1] at h2
    have hde : denoteEView s₀.store v = some hP := by
      rw [denoteE_view_eq hok.wf hw] at hh; exact hh
    cases v
    case forallE ty rest m =>
      obtain ⟨et, eb, rfl, hty, hrest⟩ := denote_forallE_inv hok.wf hw hh
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨hstep1, ho⟩ := ih rest b eb bP s₀ s₂ o hok ⟨hrest, hb⟩ h3
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨hstep1, ?_⟩
        simp only [ROp] at ho ⊢
        simp only [Expr.replacePisPw, ho, Option.map_none]
      | some x =>
        obtain ⟨y, hy, hx⟩ := ho
        obtain ⟨n, s₃, h5, h6⟩ := bindOk h4
        obtain ⟨hstep2, hn⟩ :=
          internForallEE_run hstep1.ok (denote_ext hty hstep1.ext) hx h5
        obtain ⟨rfl, rfl⟩ := pureOk h6
        refine ⟨hstep1.trans hstep2, ?_⟩
        exact ⟨.forallE et y ⟨pw⟩, by simp only [Expr.replacePisPw, hy,
          Option.map_some], hn⟩
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk h2
       refine ⟨PStep.refl hok, ?_⟩
       simp only [denoteEView] at hde
       simp only [ROp]
       first
       | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde; rfl)
       | (obtain rfl := Option.some.inj hde; rfl))

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:160-167 Expr.pisToLamsPw
The same with `.lam` in place of `.forallE`.

**CLOSED** (task #97-P3-Ind round 2): `replacePisPw_spec`'s proof with
`internLamE_run` in place of `internForallEE_run`.  The VIEW it reads is still
a `.forallE`; only the node it builds changes. -/
theorem pisToLamsPw_spec (pw : PropWhen) (k : Nat) : ∀ (h b : EIdx)
    (hP bP : Expr),
    PSpec (fun st => denoteE st h = some hP ∧ denoteE st b = some bP)
      (Arena.pisToLamsPw pw k h b)
      (ROp RE (Expr.pisToLamsPw pw k hP bP)) := by
  induction k with
  | zero =>
    intro h b hP bP s₀ s' r hok hpre hrun
    obtain ⟨_, hb⟩ := hpre
    simp only [Arena.pisToLamsPw] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, bP, rfl, hb⟩
  | succ k ih =>
    intro h b hP bP s₀ s' r hok hpre hrun
    obtain ⟨hh, hb⟩ := hpre
    simp only [Arena.pisToLamsPw] at hrun
    obtain ⟨v, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hs1, hw⟩ := view_run h1
    rw [hs1] at h2
    have hde : denoteEView s₀.store v = some hP := by
      rw [denoteE_view_eq hok.wf hw] at hh; exact hh
    cases v
    case forallE ty rest m =>
      obtain ⟨et, eb, rfl, hty, hrest⟩ := denote_forallE_inv hok.wf hw hh
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨hstep1, ho⟩ := ih rest b eb bP s₀ s₂ o hok ⟨hrest, hb⟩ h3
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨hstep1, ?_⟩
        simp only [ROp] at ho ⊢
        simp only [Expr.pisToLamsPw, ho, Option.map_none]
      | some x =>
        obtain ⟨y, hy, hx⟩ := ho
        obtain ⟨n, s₃, h5, h6⟩ := bindOk h4
        obtain ⟨hstep2, hn⟩ :=
          internLamE_run hstep1.ok (denote_ext hty hstep1.ext) hx h5
        obtain ⟨rfl, rfl⟩ := pureOk h6
        refine ⟨hstep1.trans hstep2, ?_⟩
        exact ⟨.lam et y ⟨pw⟩, by simp only [Expr.pisToLamsPw, hy,
          Option.map_some], hn⟩
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk h2
       refine ⟨PStep.refl hok, ?_⟩
       simp only [denoteEView] at hde
       simp only [ROp]
       first
       | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde; rfl)
       | (obtain rfl := Option.some.inj hde; rfl))

/-! ## The indexed family -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:189-194 structFamI
The family at its parameters and `nIdx` index variables.

**CLOSED** (task #97-P3-Ind round 2): `structFam_spec`'s composition with the
index spine appended.  Both sides spell both spines as `structPsAt`, so there
is no arithmetic step at all here. -/
theorem structFamI_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx e o : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structFamI T lps nP nIdx e o)
      (RE (ConLeche.structFamI TP lpsP nP nIdx e o)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps⟩ := hpre
  simp only [Arena.structFamI] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hus⟩ := paramLevels_spec lps lpsP s₀ s₁ us hok hlps h1
  obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hhd⟩ :=
    internConstE_run hstep1.ok (denoteN_ext hT hstep1.ext) hus h3
  obtain ⟨ps, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hps⟩ :=
    structPsAt_spec (o + e + nIdx) nP s₂ s₃ ps hstep2.ok trivial h5
  obtain ⟨is, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨hstep4, his⟩ := structPsAt_spec o nIdx s₃ s₄ is hstep3.ok trivial h7
  obtain ⟨hstep5, hr⟩ :=
    mkAppN_run (ps ++ is) _ hstep4.ok
      (denote_ext hhd (hstep3.ext.trans hstep4.ext))
      (denoteEList_append (denoteEList_ext hstep4.ext _ _ hps) his) h8
  refine ⟨hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5))), ?_⟩
  rw [ConLeche.structFamI]
  exact hr

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:196-202 structCtorResidOk
Does the constructor's residual target the family?  A `Bool` answer, so `RV`
and no target store — task #97-P3-0 §5's finding 1.

**CLOSED** (task #97-P3-Ind round 3): `paramLevels_spec` and
`structPsAt_spec` (both closed in round 2), `Bridge/ExprOps/Spine.lean`'s
closed `getAppFn_spec`/`getAppArgs_spec` in run form, and the THREE handle
comparisons — one at a handle (`beq_ehandle_eq`), one at a length
(`denoteEList_len`) and one at a handle LIST (`beq_ehandleList_eq` after
`denoteEList_take`).  Two of the three are `denoteE_inj`, DESIGN §8.3's
soundness obligation: this is the tier's first cash of it. -/
theorem structCtorResidOk_spec (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP o nIdx : Nat)
    (cbody : EIdx) (cbodyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cbody = some cbodyP)
      (Arena.structCtorResidOk T lps nP o nIdx cbody)
      (RV (ConLeche.structCtorResidOk TP lpsP nP o nIdx cbodyP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hT, hlps, hcb⟩ := hp
  simp only [Arena.structCtorResidOk] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hs1, hus⟩ := paramLevels_spec lps lpsP _ _ us hok hlps h1
  obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hs2, hhd⟩ := internConstE_run hs1.ok (denoteN_ext hT hs1.ext) hus h3
  have hcb2 : denoteE s₂.store cbody = some cbodyP :=
    denote_ext hcb (hs1.ext.trans hs2.ext)
  obtain ⟨fn, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨he3, hfn⟩ := getAppFn_run hs2.ok hcb2 h5
  rw [he3] at h6
  obtain ⟨args, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨he4, hargs⟩ := getAppArgs_run hs2.ok hcb2 h7
  rw [he4] at h8
  obtain ⟨ps, s₅, h9, h10⟩ := bindOk h8
  obtain ⟨hs5, hps⟩ := structPsAt_spec o nP _ _ ps hs2.ok trivial h9
  obtain ⟨rfl, rfl⟩ := pureOk h10
  refine ⟨hs1.trans (hs2.trans hs5), ?_⟩
  show _ = ConLeche.structCtorResidOk TP lpsP nP o nIdx cbodyP
  rw [ConLeche.structCtorResidOk,
    beq_ehandle_eq hs5.ok.wf (denote_ext hfn hs5.ext) (denote_ext hhd hs5.ext),
    beq_ehandleList_eq hs5.ok.wf
      (denoteEList_take (denoteEList_ext hs5.ext _ _ hargs) nP) hps,
    denoteEList_len (denoteEList_ext hs5.ext _ _ hargs)]

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:204-211 structMotiveTyI
The motive's type at the parameters' frame.

**CLOSED** (task #97-P3-Ind round 2): `structFamI_spec`, `internSortE_run`,
`internForallEE_run` and `replacePisPw_spec`, composed by three `bindOk`s. -/
theorem structMotiveTyI_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat) (l : LIdx) (lP : Level)
    (itele : EIdx) (iteleP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls l = some lP ∧ denoteE st itele = some iteleP)
      (Arena.structMotiveTyI T lps nP nIdx l itele)
      (ROp RE (ConLeche.structMotiveTyI TP lpsP nP nIdx lP iteleP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hl, hit⟩ := hpre
  simp only [Arena.structMotiveTyI] at hrun
  obtain ⟨fam, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hfam⟩ :=
    structFamI_spec T TP lps lpsP nP nIdx 0 0 s₀ s₁ fam hok ⟨hT, hlps⟩ h1
  obtain ⟨sh, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hsh⟩ :=
    internSortE_run hstep1.ok (denoteL_ext hl hstep1.ext) h3
  obtain ⟨body, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hbody⟩ :=
    internForallEE_run hstep2.ok (denote_ext hfam hstep2.ext) hsh h5
  obtain ⟨hstep4, hr⟩ :=
    replacePisPw_spec .never nIdx itele body iteleP _ s₃ s' r hstep3.ok
      ⟨denote_ext hit (hstep1.ext.trans (hstep2.ext.trans hstep3.ext)), hbody⟩
      h6
  exact ⟨hstep1.trans (hstep2.trans (hstep3.trans hstep4)), hr⟩

/-! ## The recogniser -/

/-! ### The recogniser, and the six shapes that answer `false`

`structShape` is the tier's group-2 gateway (task #97-P3-Ind round 4 §R4.6:
seventeen statements wait on it).  Its proof is the arena's run inverted
against con-leche's `match`, and the two sides meet at six places where the
arena answers `false` without computing the rest: the three telescopes, the
type former's residual, the motive's domain, the minor premise's domain and
the major's.  Each of those is one `simp only` over `structShape_unfold` plus
whatever constructor the arena's `view` dispatch has just named, and each is
stated separately so the ten-way dispatches in the proof close with one
`all_goals`.

The one place the two sides are NOT in step is the `if large`: the
do-elaborator duplicates everything after `let want ← if large then … else …`
into both arms.  `Bridge/Inductives/Rel.lean`'s `am_if_bind` puts the `if`
back in front of the bind, so the minor premise and the major domain are
inverted once rather than twice. -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
— **the pure side, once the three telescopes are known**: con-leche's `match`
on the three `stripPis` answers, selected.  Everything below reads the five
conjuncts through this one equation, so the recogniser's body is unfolded in
exactly one place. -/
theorem structShape_unfold {T C : ConLeche.Name} {lps : List ConLeche.Name}
    {elim : ConLeche.Name} {large : Bool} {nP nF : Nat}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cbody rbody : Expr}
    {tty cty rty : Expr}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cbody))
    (hr : rty.stripPis (nP + 3) = some (rxs, rbody)) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty =
      (cbody == ConLeche.structFam T lps nP nF &&
       rbody == Expr.app (.bvar 2) (.bvar 0) &&
       (match rxs[nP]? with
        | some (.forallE mmaj (.sort s') _, _) =>
          (if large then s' == .param elim else s' == .zero) &&
            mmaj == ConLeche.structFam T lps nP 0
        | _ => false) &&
       (match rxs[nP + 1]? with
        | some (mindom, _) =>
          match mindom.stripPis nF with
          | some (_, mbody) =>
            mbody == Expr.app (.bvar nF) (ConLeche.structCtorSpine C lps nP nF)
          | none => false
        | none => false) &&
       (match rxs[nP + 2]? with
        | some (majdom, _) => majdom == ConLeche.structFam T lps nP 2
        | none => false)) := by
  simp only [ConLeche.structShape, ht, hc, hr]
  rfl

/-- con-leche: none — the type former's telescope does not peel: `false`. -/
theorem structShape_false_t {T C : ConLeche.Name} {lps : List ConLeche.Name}
    {elim : ConLeche.Name} {large : Bool} {nP nF : Nat} {tty cty rty : Expr}
    (ht : tty.stripPis nP = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  simp only [ConLeche.structShape, ht]

/-- con-leche: none — the constructor's telescope does not peel: `false`. -/
theorem structShape_false_c {T C : ConLeche.Name} {lps : List ConLeche.Name}
    {elim : ConLeche.Name} {large : Bool} {nP nF : Nat} {tty cty rty : Expr}
    {txs : List (Expr × BinderMeta)} {tb : Expr}
    (ht : tty.stripPis nP = some (txs, tb))
    (hc : cty.stripPis (nP + nF) = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  simp only [ConLeche.structShape, ht, hc]

/-- con-leche: none — the recursor's telescope does not peel: `false`. -/
theorem structShape_false_r {T C : ConLeche.Name} {lps : List ConLeche.Name}
    {elim : ConLeche.Name} {large : Bool} {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs : List (Expr × BinderMeta)} {tb cb : Expr}
    (ht : tty.stripPis nP = some (txs, tb))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  simp only [ConLeche.structShape, ht, hc, hr]

/-- con-leche: none — the type former's RESIDUAL is not a `Sort`: `false`.
The arena decides this on the node's TAG (`view tbody`) where con-leche
decides it on the term, which is why the hypothesis is the negative fact
`Bridge/ExprOps/Spine.lean`'s `denoteEView_not_sort` supplies. -/
theorem structShape_false_sort {T C : ConLeche.Name} {lps : List ConLeche.Name}
    {elim : ConLeche.Name} {large : Bool} {nP nF : Nat} {tty cty rty : Expr}
    {txs : List (Expr × BinderMeta)} {tb : Expr}
    (ht : tty.stripPis nP = some (txs, tb)) (hns : ∀ l, tb ≠ .sort l) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  simp only [ConLeche.structShape, ht]
  cases tb
  case sort l => exact absurd rfl (hns l)
  all_goals rfl

/-- con-leche: none — the recursor has no `nP`-th binder: `false`. -/
theorem structShape_false_motive_none {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {elim : ConLeche.Name} {large : Bool}
    {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cb rb : Expr}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = some (rxs, rb))
    (hm : rxs[nP]? = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  rw [structShape_unfold ht hc hr]; simp [hm]

/-- con-leche: none — the motive's domain is not a `∀` with a `Sort`
codomain: `false`.  Two `view` dispatches on the arena side, one `Expr`
pattern on con-leche's. -/
theorem structShape_false_motive {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {elim : ConLeche.Name} {large : Bool}
    {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cb rb md : Expr}
    {m : BinderMeta}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = some (rxs, rb))
    (hm : rxs[nP]? = some (md, m))
    (hns : ∀ a b c, md ≠ .forallE a (.sort b) c) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  rw [structShape_unfold ht hc hr]
  simp only [hm]
  cases md
  case forallE a b c =>
    cases b
    case sort u => exact absurd rfl (hns a u c)
    all_goals simp
  all_goals simp

/-- con-leche: none — the recursor has no `nP+1`-th binder: `false`. -/
theorem structShape_false_minor_none {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {elim : ConLeche.Name} {large : Bool}
    {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cb rb : Expr}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = some (rxs, rb))
    (hm : rxs[nP + 1]? = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  rw [structShape_unfold ht hc hr]; simp [hm]

/-- con-leche: none — the minor premise's domain does not peel `nF`
binders: `false`. -/
theorem structShape_false_minor_strip {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {elim : ConLeche.Name} {large : Bool}
    {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cb rb mid : Expr}
    {m : BinderMeta}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = some (rxs, rb))
    (hm : rxs[nP + 1]? = some (mid, m))
    (hs : mid.stripPis nF = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  rw [structShape_unfold ht hc hr]; simp [hm, hs]

/-- con-leche: none — the recursor has no `nP+2`-th binder: `false`. -/
theorem structShape_false_major_none {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {elim : ConLeche.Name} {large : Bool}
    {nP nF : Nat} {tty cty rty : Expr}
    {txs cxs rxs : List (Expr × BinderMeta)} {l : Level} {cb rb : Expr}
    (ht : tty.stripPis nP = some (txs, .sort l))
    (hc : cty.stripPis (nP + nF) = some (cxs, cb))
    (hr : rty.stripPis (nP + 3) = some (rxs, rb))
    (hm : rxs[nP + 2]? = none) :
    ConLeche.structShape T C lps elim large nP nF tty cty rty = false := by
  rw [structShape_unfold ht hc hr]; simp [hm]

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
The shape facts the model reads off the stored (annotated) types.  A `Bool`
answer.

**CLOSED** (task #97-P3-Ind round 5).  `stripPis_pstep` three times, the
ten-way `view` dispatch at the type former's residual, at the motive's domain
and at its codomain, `structFam_spec` three times (at `nF`, at `0` and at
`2`), `structCtorSpine_spec`, `internBVarE_run`/`internAppE_run`,
`internParamL_run`/`internZeroL_run` for the elimination level, and five
handle comparisons — four through `denoteE_inj` (`beq_ehandle_eq`) and one,
the motive's codomain, through `denoteL_inj` (`beq_lhandle_eq`, stated this
round in `Rel.lean`).  The indexed binder reads are `denoteBinders_getElem?`,
the `Option`-carrying half of round 4's `denoteBinders_getD`. -/
theorem structShape_spec (T C : NIdx) (TP CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nF : Nat) (tty cty rty : EIdx)
    (ttyP ctyP rtyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteE st cty = some ctyP ∧ denoteE st rty = some rtyP)
      (Arena.structShape T C lps elim large nP nF tty cty rty)
      (RV (ConLeche.structShape TP CP lpsP elimP large nP nF ttyP ctyP rtyP)) := by
  intro s₀ s' r hok hpre hz
  obtain ⟨hT, hC, hlps, helim, htty, hcty, hrty⟩ := hpre
  simp only [Arena.structShape] at hz
  obtain ⟨tq, sa, ka, hz1⟩ := bindOk hz
  obtain ⟨hsa, htq⟩ := stripPis_pstep hok htty ka
  rw [hsa] at hz1
  obtain ⟨cq, sb, kb, hz2⟩ := bindOk hz1
  obtain ⟨hsb, hcq⟩ := stripPis_pstep hok hcty kb
  rw [hsb] at hz2
  obtain ⟨rq, sc, kc, hz3⟩ := bindOk hz2
  obtain ⟨hsc, hrq⟩ := stripPis_pstep hok hrty kc
  rw [hsc] at hz3
  rcases tq with _ | ⟨tbs, tbody⟩
  · obtain ⟨rfl, rfl⟩ := pureOk hz3
    exact ⟨PStep.refl hok, (structShape_false_t (stripPis_none htq)).symm⟩
  obtain ⟨txs, tbodyP, hspt, htbs, htbody⟩ := denoteBP_someB htq
  rcases cq with _ | ⟨cbs, cbody⟩
  · obtain ⟨rfl, rfl⟩ := pureOk hz3
    exact ⟨PStep.refl hok, (structShape_false_c hspt (stripPis_none hcq)).symm⟩
  obtain ⟨cxs, cbodyP, hspc, hcbs, hcbody⟩ := denoteBP_someB hcq
  rcases rq with _ | ⟨rbs, rbody⟩
  · obtain ⟨rfl, rfl⟩ := pureOk hz3
    exact ⟨PStep.refl hok, (structShape_false_r hspt hspc (stripPis_none hrq)).symm⟩
  obtain ⟨rxs, rbodyP, hspr, hrbs, hrbody⟩ := denoteBP_someB hrq
  obtain ⟨tv, sd, kd, hz4⟩ := bindOk hz3
  obtain ⟨hsd, htv⟩ := view_run kd
  rw [hsd] at hz4
  have htbv : denoteEView s₀.store tv = some tbodyP := by
    rw [← denoteE_view_eq hok.wf htv]; exact htbody
  cases tv
  case sort tu =>
    obtain ⟨tl, htbEq, htul⟩ := denote_sort_inv hok.wf htv htbody
    subst htbEq
    obtain ⟨fam, s1, k1, hz5⟩ := bindOk hz4
    obtain ⟨p1, hfam⟩ := structFam_spec T TP lps lpsP nP nF s₀ s1 fam hok ⟨hT, hlps⟩ k1
    obtain ⟨b2, s2, k2, hz6⟩ := bindOk hz5
    obtain ⟨p2, hb2⟩ := internBVarE_run p1.ok k2
    obtain ⟨b0, s3, k3, hz7⟩ := bindOk hz6
    obtain ⟨p3, hb0⟩ := internBVarE_run p2.ok k3
    obtain ⟨wnt, s4, k4, hz8⟩ := bindOk hz7
    obtain ⟨p4, hwnt⟩ := internAppE_run p3.ok (denote_ext hb2 p3.ext) hb0 k4
    have q4 : PStep s₀ s4 := p1.trans (p2.trans (p3.trans p4))
    have e1 : (cbody == fam) = (cbodyP == ConLeche.structFam TP lpsP nP nF) :=
      beq_ehandle_eq q4.ok.wf (denote_ext hcbody q4.ext)
        (denote_ext hfam (p2.ext.trans (p3.ext.trans p4.ext)))
    have e2 : (rbody == wnt) = (rbodyP == Expr.app (.bvar 2) (.bvar 0)) :=
      beq_ehandle_eq q4.ok.wf (denote_ext hrbody q4.ext) hwnt
    rw [e1, e2] at hz8
    split at hz8
    case isTrue hcond =>
      have hAB : (cbodyP == ConLeche.structFam TP lpsP nP nF &&
          rbodyP == Expr.app (Expr.bvar 2) (Expr.bvar 0)) = false := by
        simp only [Bool.not_eq_true'] at hcond; exact hcond
      obtain ⟨rfl, rfl⟩ := pureOk hz8
      refine ⟨q4, ?_⟩
      show (false : Bool) = _
      rw [structShape_unfold hspt hspc hspr]
      simp [hAB]
    case isFalse hcond =>
      have hAB : (cbodyP == ConLeche.structFam TP lpsP nP nF &&
          rbodyP == Expr.app (Expr.bvar 2) (Expr.bvar 0)) = true := by
        simp only [Bool.not_eq_true, Bool.not_eq_false'] at hcond; exact hcond
      obtain ⟨hgetA, hgetB⟩ := denoteBinders_getElem? hrbs nP
      cases hm : rbs[nP]? with
      | none =>
        rw [hm] at hz8
        obtain ⟨y1, s5, k5, hz9⟩ := bindOk hz8
        obtain ⟨rfl, rfl⟩ := pureOk k5
        split at hz9
        case isFalse hbad => exact absurd rfl hbad
        case isTrue _ =>
          obtain ⟨rfl, rfl⟩ := pureOk hz9
          exact ⟨q4, (structShape_false_motive_none hspt hspc hspr (hgetB hm)).symm⟩
      | some mp =>
        obtain ⟨mdom, mbm⟩ := mp
        obtain ⟨mdomP, hmx, hmdom⟩ := hgetA mdom mbm hm
        rw [hm] at hz8
        obtain ⟨mv, s5, k5, hz9⟩ := bindOk hz8
        obtain ⟨hs5, hmv⟩ := view_run k5
        rw [hs5] at hz9
        have hmdom4 : denoteE s4.store mdom = some mdomP := denote_ext hmdom q4.ext
        have hmdv : denoteEView s4.store mv = some mdomP := by
          rw [← denoteE_view_eq q4.ok.wf hmv]; exact hmdom4
        cases mv
        case forallE mty mcod mm =>
          obtain ⟨mtyP, mcodP, hmdEq, hmty, hmcod⟩ :=
            denote_forallE_inv q4.ok.wf hmv hmdom4
          obtain ⟨mv2, s6, k6, hz10⟩ := bindOk hz9
          obtain ⟨hs6, hmv2⟩ := view_run k6
          rw [hs6] at hz10
          have hmcv : denoteEView s4.store mv2 = some mcodP := by
            rw [← denoteE_view_eq q4.ok.wf hmv2]; exact hmcod
          cases mv2
          case sort lu =>
            obtain ⟨lvl, hmcEq, hlvl⟩ := denote_sort_inv q4.ok.wf hmv2 hmcod
            subst hmcEq
            subst hmdEq
            simp only [am_if_bind] at hz10
            obtain ⟨wl, s7, k7, hz11⟩ := bindOk hz10
            have hwl : PStep s4 s7 ∧ denoteL s7.store.ls wl =
                some (if large then Level.param elimP else Level.zero) := by
              by_cases hL : large = true
              · rw [if_pos hL] at k7 ⊢
                exact internParamL_run q4.ok (denoteN_ext helim q4.ext) k7
              · rw [if_neg hL] at k7 ⊢
                exact internZeroL_run q4.ok k7
            obtain ⟨p7, hwld⟩ := hwl
            have q7 : PStep s₀ s7 := q4.trans p7
            obtain ⟨fam0, s8, k8, hz12⟩ := bindOk hz11
            obtain ⟨p8, hfam0⟩ := structFam_spec T TP lps lpsP nP 0 s7 s8 fam0 p7.ok
              ⟨denoteN_ext hT q7.ext, denoteNListE_ext q7.ext lps lpsP hlps⟩ k8
            have q8 : PStep s₀ s8 := q7.trans p8
            obtain ⟨y2, s9, k9, hz13⟩ := bindOk hz12
            obtain ⟨rfl, rfl⟩ := pureOk k9
            have e3 : (lu == wl) =
                (lvl == (if large then Level.param elimP else Level.zero)) :=
              beq_lhandle_eq q8.ok.wf (denoteL_ext hlvl (p7.ext.trans p8.ext))
                (denoteL_ext hwld p8.ext)
            have e4 : (mty == fam0) = (mtyP == ConLeche.structFam TP lpsP nP 0) :=
              beq_ehandle_eq q8.ok.wf (denote_ext hmty (p7.ext.trans p8.ext)) hfam0
            have ecl : (lvl == (if large then Level.param elimP else Level.zero)) =
                (if large then lvl == Level.param elimP else lvl == Level.zero) := by
              cases large <;> simp
            split at hz13
            case isTrue hbad =>
              have hy2 : (lu == wl && mty == fam0) = false := by
                simp only [Bool.not_eq_true'] at hbad; exact hbad
              obtain ⟨rfl, rfl⟩ := pureOk hz13
              refine ⟨q8, ?_⟩
              show (false : Bool) = _
              rw [structShape_unfold hspt hspc hspr]
              simp only [hmx, ← ecl, ← e3, ← e4, hy2]
              simp
            case isFalse hgood =>
              have hy2 : (lu == wl && mty == fam0) = true := by
                simp only [Bool.not_eq_true, Bool.not_eq_false'] at hgood; exact hgood
              have hMval : ((if large then lvl == Level.param elimP
                  else lvl == Level.zero) &&
                  (mtyP == ConLeche.structFam TP lpsP nP 0)) = true := by
                rw [← ecl, ← e3, ← e4]; exact hy2
              obtain ⟨hgetA1, hgetB1⟩ := denoteBinders_getElem? hrbs (nP + 1)
              cases hmin : rbs[nP + 1]? with
              | none =>
                rw [hmin] at hz13
                obtain ⟨y3, s10, k10, hz14⟩ := bindOk hz13
                obtain ⟨rfl, rfl⟩ := pureOk k10
                split at hz14
                case isFalse hbad => exact absurd rfl hbad
                case isTrue _ =>
                  obtain ⟨rfl, rfl⟩ := pureOk hz14
                  exact ⟨q8, (structShape_false_minor_none hspt hspc hspr
                    (hgetB1 hmin)).symm⟩
              | some mq =>
                obtain ⟨mid, mbm1⟩ := mq
                obtain ⟨midP, hminx, hmid⟩ := hgetA1 mid mbm1 hmin
                rw [hmin] at hz13
                obtain ⟨sq, s10, k10, hz14⟩ := bindOk hz13
                obtain ⟨hs10, hsq⟩ :=
                  stripPis_pstep q8.ok (denote_ext hmid q8.ext) k10
                rw [hs10] at hz14
                rcases sq with _ | ⟨sbs, sbody⟩
                · obtain ⟨y3, s11, k11, hz15⟩ := bindOk hz14
                  obtain ⟨rfl, rfl⟩ := pureOk k11
                  split at hz15
                  case isFalse hbad => exact absurd rfl hbad
                  case isTrue _ =>
                    obtain ⟨rfl, rfl⟩ := pureOk hz15
                    exact ⟨q8, (structShape_false_minor_strip hspt hspc hspr hminx
                      (stripPis_none hsq)).symm⟩
                obtain ⟨sxs, sbodyP, hsps, hsbs, hsbody⟩ := denoteBP_someB hsq
                obtain ⟨hd, s11, k11, hz15⟩ := bindOk hz14
                obtain ⟨p11, hhd⟩ := internBVarE_run q8.ok k11
                obtain ⟨sp, s12, k12, hz16⟩ := bindOk hz15
                obtain ⟨p12, hsp⟩ := structCtorSpine_spec C CP lps lpsP nP nF s11 s12
                  sp p11.ok ⟨denoteN_ext hC (q8.ext.trans p11.ext),
                    denoteNListE_ext (q8.ext.trans p11.ext) lps lpsP hlps⟩ k12
                obtain ⟨wm, s13, k13, hz17⟩ := bindOk hz16
                obtain ⟨p13, hwm⟩ := internAppE_run p12.ok
                  (denote_ext hhd p12.ext) hsp k13
                have q13 : PStep s₀ s13 := q8.trans (p11.trans (p12.trans p13))
                obtain ⟨y3, s14, k14, hz18⟩ := bindOk hz17
                obtain ⟨rfl, rfl⟩ := pureOk k14
                have e5 : (sbody == wm) = (sbodyP ==
                    Expr.app (.bvar nF) (ConLeche.structCtorSpine CP lpsP nP nF)) :=
                  beq_ehandle_eq q13.ok.wf
                    (denote_ext hsbody
                      (p11.ext.trans (p12.ext.trans p13.ext))) hwm
                split at hz18
                case isTrue hbad =>
                  have hy3 : (sbody == wm) = false := by
                    simp only [Bool.not_eq_true'] at hbad; exact hbad
                  obtain ⟨rfl, rfl⟩ := pureOk hz18
                  refine ⟨q13, ?_⟩
                  show (false : Bool) = _
                  rw [structShape_unfold hspt hspc hspr]
                  simp only [hmx, hminx, hsps, ← e5, hy3]
                  simp
                case isFalse hgood3 =>
                  have hy3 : (sbody == wm) = true := by
                    simp only [Bool.not_eq_true, Bool.not_eq_false'] at hgood3
                    exact hgood3
                  have hMinval : (sbodyP == Expr.app (.bvar nF)
                      (ConLeche.structCtorSpine CP lpsP nP nF)) = true := by
                    rw [← e5]; exact hy3
                  obtain ⟨hgetA2, hgetB2⟩ := denoteBinders_getElem? hrbs (nP + 2)
                  cases hmaj : rbs[nP + 2]? with
                  | none =>
                    rw [hmaj] at hz18
                    obtain ⟨rfl, rfl⟩ := pureOk hz18
                    exact ⟨q13, (structShape_false_major_none hspt hspc hspr
                      (hgetB2 hmaj)).symm⟩
                  | some jq =>
                    obtain ⟨majdom, mbm2⟩ := jq
                    obtain ⟨majdomP, hmajx, hmajd⟩ := hgetA2 majdom mbm2 hmaj
                    rw [hmaj] at hz18
                    obtain ⟨fam2, s15, k15, hz19⟩ := bindOk hz18
                    obtain ⟨p15, hfam2⟩ := structFam_spec T TP lps lpsP nP 2 _ _
                      fam2 q13.ok ⟨denoteN_ext hT q13.ext,
                        denoteNListE_ext q13.ext lps lpsP hlps⟩ k15
                    obtain ⟨rfl, rfl⟩ := pureOk hz19
                    have q15 : PStep s₀ _ := q13.trans p15
                    have e6 : (majdom == fam2) =
                        (majdomP == ConLeche.structFam TP lpsP nP 2) :=
                      beq_ehandle_eq q15.ok.wf (denote_ext hmajd q15.ext) hfam2
                    refine ⟨q15, ?_⟩
                    show (majdom == fam2) = _
                    rw [structShape_unfold hspt hspc hspr]
                    simp only [hmx, hminx, hsps, hmajx, hAB, hMval, hMinval, e6,
                      Bool.and_true, Bool.true_and]
          all_goals
            (obtain ⟨rfl, rfl⟩ := pureOk hz10
             exact ⟨q4, (structShape_false_motive hspt hspc hspr hmx
              (by intro a b c h
                  rw [hmdEq] at h
                  simp only [Expr.forallE.injEq] at h
                  exact absurd h.2.1
                    (ExprOps.denoteEView_not_sort hmcv (by simp) b))).symm⟩)
        all_goals
          (obtain ⟨rfl, rfl⟩ := pureOk hz9
           exact ⟨q4, (structShape_false_motive hspt hspc hspr hmx
             (fun a b c h =>
               ExprOps.denoteEView_not_forallE hmdv (by simp) a (.sort b) c h)).symm⟩)
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk hz4
     exact ⟨PStep.refl hok, (structShape_false_sort hspt
       (ExprOps.denoteEView_not_sort htbv (by simp))).symm⟩)

/-! ### The recogniser's dispatch (task #97-P3-Ind round 6)

`structPartsCore?_spec` (core grade) and `structPartsCore?_isSome` (pure
grade, pin licence) share ONE inversion, `structPartsCore?_run`: its frame is
`PStep` at `StateOK` + `PinsOK`, and its answer relation carries the whole
record under a `CheckOK` hypothesis at the INITIAL state — the one field that
needs it is `isProp`, `lvlEq?`'s verdict, and `CheckOK` travels to the
`lvlEq?` call through `PStep.toCore`.  `ROp`'s two-sidedness does not depend
on the relation, which is exactly the `isSome` half. -/

/-- con-leche: none — a three-constant block's denotation, forwards: the
recogniser's pattern on the handle side names the same pattern on the pure
side, field by field. -/
theorem denoteCIList_struct3 {st : EStore} {cvT : IConstantVal} {caps : IIndCaps}
    {cvC : IConstantVal} {nP nF : Nat} {cvR : IConstantVal} {mI rP : Nat}
    {rule : IRecRule} {blockP : List ConstantInfo}
    (h : Frontend.denoteCIList st
      [.indInfo cvT caps, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] = some blockP) :
    ∃ cvTP capsP cvCP cvRP ruleP,
      blockP = [.indInfo cvTP capsP, .ctorInfo cvCP nP nF, .recInfo cvRP mI rP [ruleP]] ∧
      Frontend.denoteCV st cvT = some cvTP ∧ Frontend.denoteCV st cvC = some cvCP ∧
      Frontend.denoteCV st cvR = some cvRP ∧ Frontend.denoteRule st rule = some ruleP := by
  simp only [Frontend.denoteCIList, Frontend.denoteCI, Frontend.denoteRules] at h
  cases h1 : Frontend.denoteCV st cvT <;> cases h2 : Frontend.denoteCaps st caps <;>
    cases h3 : Frontend.denoteCV st cvC <;> cases h4 : Frontend.denoteCV st cvR <;>
    cases h5 : Frontend.denoteRule st rule <;> simp_all
  subst h
  exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-- con-leche: none — a denoting cons is a cons of denotations. -/
theorem denoteCIList_cons_eq {st : EStore} {c : IConstantInfo}
    {cs : List IConstantInfo} {ys : List ConstantInfo}
    (h : Frontend.denoteCIList st (c :: cs) = some ys) :
    ∃ x xs, ys = x :: xs ∧ Frontend.denoteCI st c = some x ∧
      Frontend.denoteCIList st cs = some xs := by
  simp only [Frontend.denoteCIList] at h
  cases h1 : Frontend.denoteCI st c <;> cases h2 : Frontend.denoteCIList st cs <;>
    simp_all

/-- con-leche: none — the same at a rule list. -/
theorem denoteRules_cons_eq {st : EStore} {c : IRecRule}
    {cs : List IRecRule} {ys : List RecRule}
    (h : Frontend.denoteRules st (c :: cs) = some ys) :
    ∃ x xs, ys = x :: xs ∧ Frontend.denoteRule st c = some x ∧
      Frontend.denoteRules st cs = some xs := by
  simp only [Frontend.denoteRules] at h
  cases h1 : Frontend.denoteRule st c <;> cases h2 : Frontend.denoteRules st cs <;>
    simp_all

/-- con-leche: none — `denoteCI` preserves the constant's kind: the three
kinds the recogniser's pattern names. -/
theorem denoteCI_ind_shape {st : EStore} {a : IConstantInfo} {v : ConstantVal}
    {c : IndCaps} (h : Frontend.denoteCI st a = some (.indInfo v c)) :
    ∃ v' c', a = .indInfo v' c' := by
  cases a <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h <;>
    (try split at h) <;> simp_all

theorem denoteCI_ctor_shape {st : EStore} {a : IConstantInfo} {v : ConstantVal}
    {nP nF : Nat} (h : Frontend.denoteCI st a = some (.ctorInfo v nP nF)) :
    ∃ v', a = .ctorInfo v' nP nF := by
  cases a <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h <;>
    (try split at h) <;> simp_all
  obtain ⟨_, _, _, h2, h3⟩ := h; exact ⟨h2, h3⟩

theorem denoteCI_rec_shape {st : EStore} {a : IConstantInfo} {v : ConstantVal}
    {mI rP : Nat} {rs : List RecRule} (h : Frontend.denoteCI st a = some (.recInfo v mI rP rs)) :
    ∃ v' rs', a = .recInfo v' mI rP rs' ∧ Frontend.denoteRules st rs' = some rs := by
  cases a <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h <;>
    (try split at h) <;> simp_all
  rename_i hr
  exact ⟨_, _, ⟨rfl, rfl⟩, hr⟩

/-- con-leche: none — and backwards: a block that DENOTES the pure pattern
has the handle pattern. -/
theorem denoteCIList_struct3_inv {st : EStore} {block : List IConstantInfo}
    {cvTP : ConstantVal} {capsP : IndCaps} {cvCP : ConstantVal} {nP nF : Nat}
    {cvRP : ConstantVal} {mI rP : Nat} {ruleP : RecRule}
    (h : Frontend.denoteCIList st block =
      some [.indInfo cvTP capsP, .ctorInfo cvCP nP nF, .recInfo cvRP mI rP [ruleP]]) :
    ∃ cvT caps cvC cvR rule,
      block = [.indInfo cvT caps, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] := by
  rcases block with _ | ⟨a, bs⟩
  · simp [Frontend.denoteCIList] at h
  obtain ⟨x1, r1, e1, d1, t1⟩ := denoteCIList_cons_eq h
  simp only [List.cons.injEq] at e1; obtain ⟨rfl, rfl⟩ := e1
  rcases bs with _ | ⟨b, cs⟩
  · simp [Frontend.denoteCIList] at t1
  obtain ⟨x2, r2, e2, d2, t2⟩ := denoteCIList_cons_eq t1
  simp only [List.cons.injEq] at e2; obtain ⟨rfl, rfl⟩ := e2
  rcases cs with _ | ⟨c, ds⟩
  · simp [Frontend.denoteCIList] at t2
  obtain ⟨x3, r3, e3, d3, t3⟩ := denoteCIList_cons_eq t2
  simp only [List.cons.injEq] at e3; obtain ⟨rfl, rfl⟩ := e3
  rcases ds with _ | ⟨d, es⟩
  · obtain ⟨v1, c1, rfl⟩ := denoteCI_ind_shape d1
    obtain ⟨v2, rfl⟩ := denoteCI_ctor_shape d2
    obtain ⟨v3, rs, rfl, hrs⟩ := denoteCI_rec_shape d3
    rcases rs with _ | ⟨q1, qs⟩
    · simp [Frontend.denoteRules] at hrs
    rcases qs with _ | ⟨q2, qs⟩
    · exact ⟨_, _, _, _, _, rfl⟩
    · obtain ⟨_, ys, e5, _, t5⟩ := denoteRules_cons_eq hrs
      simp only [List.cons.injEq] at e5; obtain ⟨-, rfl⟩ := e5
      obtain ⟨_, _, e6, _, _⟩ := denoteRules_cons_eq t5
      simp at e6
  · obtain ⟨_, _, e4, _, _⟩ := denoteCIList_cons_eq t3
    simp at e4

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
— **the recogniser's run, inverted once**, for both of its statements (see the
section note). -/
theorem structPartsCore?_run (block : List IConstantInfo)
    (blockP : List ConstantInfo) (s₀ s' : AState) (r : Option Arena.StructParts)
    (hok : StateOK s₀) (hpin : PinsOK s₀)
    (hb : Frontend.denoteCIList s₀.store block = some blockP)
    (hrun : Arena.structPartsCore? block s₀ = .ok (r, s')) :
    PStep s₀ s' ∧
      ROp (fun q st p => ∀ (μ : CheckMode) (env : Env) (fe : IFEnv),
          CheckOK μ env fe s₀ → SPartsRel st p q)
        (ConLeche.structPartsCore? blockP) s'.store r := by
  unfold Arena.structPartsCore? at hrun
  split at hrun
  case h_2 hne =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show ConLeche.structPartsCore? blockP = none
    unfold ConLeche.structPartsCore?
    split
    · obtain ⟨_, _, _, _, _, rfl⟩ := denoteCIList_struct3_inv hb
      exact absurd rfl (hne _ _ _ _ _ _ _ _ _)
    · rfl
  rename_i cvT caps cvC nP nF cvR mI rP rule
  obtain ⟨cvTP, capsP, cvCP, cvRP, ruleP, rfl, hcvT, hcvC, hcvR, hrule⟩ :=
    denoteCIList_struct3 hb
  have hT := denoteCV_name hcvT
  have hC := denoteCV_name hcvC
  have hR := denoteCV_name hcvR
  have hlps := denoteCV_lps hcvT
  have hClps := denoteCV_lps hcvC
  have hRlps := denoteCV_lps hcvR
  have hTty := denoteCV_type hcvT
  have hCty := denoteCV_type hcvC
  have hRty := denoteCV_type hcvR
  obtain ⟨hrc, hnf⟩ := denoteRule_ctor hrule
  have hrhs := denoteRule_rhs hrule
  dsimp only at hrun
  obtain ⟨recName, s1, k1, hz1⟩ := bindOk hrun
  obtain ⟨p1, hrec⟩ := internStrN_run (str := "rec") hok hT k1
  obtain ⟨reserved, s2, k2, hz2⟩ := bindOk hz1
  obtain ⟨p2, hres⟩ := reservedBasisNames_pstep p1.ok (hpin.mono p1.ext p1.pins) k2
  have q2 : PStep s₀ s2 := p1.trans p2
  obtain ⟨sl, s3, k3, hz3⟩ := bindOk hz2
  obtain ⟨hs3, hsl⟩ := stripLams_pstep q2.ok (denote_ext hrhs q2.ext) k3
  subst hs3
  -- the eight name/list comparisons of the guard, at any later store
  have guard : ∀ st : EStore, StoreWF st → Ext s3.store st →
      (cvR.name == recName) = (cvRP.name == cvTP.name.str "rec") ∧
      (cvC.levelParams == cvT.levelParams) = (cvCP.levelParams == cvTP.levelParams) ∧
      reserved.contains cvT.name = ConLeche.reservedBasisNames.contains cvTP.name ∧
      reserved.contains cvC.name = ConLeche.reservedBasisNames.contains cvCP.name ∧
      reserved.contains cvR.name = ConLeche.reservedBasisNames.contains cvRP.name ∧
      (rule.ctor == cvC.name) = (ruleP.ctor == cvCP.name) := by
    intro st hwf hx
    have x2 : Ext s₀.store st := q2.ext.trans hx
    have hres' := denoteNListE_ext hx _ _ hres
    refine ⟨beq_handle_eq hwf (denoteN_ext hR x2)
        (denoteN_ext hrec (p2.ext.trans hx)),
      beq_nhandleList_eq hwf (denoteNListE_ext x2 _ _ hClps)
        (denoteNListE_ext x2 _ _ hlps),
      denoteNList_contains hwf _ _ hres' _ _ (denoteN_ext hT x2),
      denoteNList_contains hwf _ _ hres' _ _ (denoteN_ext hC x2),
      denoteNList_contains hwf _ _ hres' _ _ (denoteN_ext hR x2),
      beq_handle_eq hwf (denoteN_ext hrc x2) (denoteN_ext hC x2)⟩
  rcases sl with _ | ⟨rbs, rbody⟩
  · -- the rule's right-hand side does not peel: `rhsOk = false`
    have hslP : ruleP.rhs.stripLams (nP + 2 + nF) = none := (Option.some.inj hsl).symm
    obtain ⟨y, s4, k4, hz4⟩ := bindOk hz3
    obtain ⟨rfl, rfl⟩ := pureOk k4
    simp only [Bool.and_false] at hz4
    obtain ⟨rfl, rfl⟩ := pureOk hz4
    refine ⟨q2, ?_⟩
    show ConLeche.structPartsCore? _ = none
    simp only [ConLeche.structPartsCore?, hslP, Bool.and_false]
    rfl
  obtain ⟨_, rbodyP, hslP, hrb⟩ := denoteBP_some' hsl
  obtain ⟨want, s4, k4, hz4⟩ := bindOk hz3
  obtain ⟨p4, hwant⟩ := structRuleBody_spec nF s3 s4 want q2.ok trivial k4
  have q4 : PStep s₀ s4 := q2.trans p4
  obtain ⟨y, s5, k5, hz5⟩ := bindOk hz4
  obtain ⟨rfl, hs5⟩ := pureOk k5
  rw [hs5] at hz5
  have erhs : (rbody == want) = (rbodyP == ConLeche.structRuleBody nF) :=
    beq_ehandle_eq q4.ok.wf (denote_ext hrb p4.ext) hwant
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := guard s4.store q4.ok.wf p4.ext
  rw [g1, g2, g3, g4, g5, g6, hnf, erhs] at hz5
  simp only [ConLeche.structPartsCore?, hslP]
  split at hz5
  case isFalse hc =>
    obtain ⟨rfl, rfl⟩ := pureOk hz5
    refine ⟨q4, ?_⟩
    show _ = none
    rw [if_neg hc]
  case isTrue hc =>
  rw [if_pos hc]
  obtain ⟨tq, s6, k6, hz6⟩ := bindOk hz5
  obtain ⟨hs6, htq⟩ := stripPis_pstep q4.ok (denote_ext hTty q4.ext) k6
  rw [hs6] at hz6
  rcases tq with _ | ⟨tbs, tbody⟩
  · obtain ⟨rfl, rfl⟩ := pureOk hz6
    refine ⟨q4, ?_⟩
    show _ = none
    rw [stripPis_none htq]
  obtain ⟨txs, tbodyP, hspt, -, htbody⟩ := denoteBP_someB htq
  rw [hspt]
  obtain ⟨tv, s7, k7, hz7⟩ := bindOk hz6
  obtain ⟨hs7, htv⟩ := view_run k7
  rw [hs7] at hz7
  have htbv : denoteEView s4.store tv = some tbodyP := by
    rw [← denoteE_view_eq q4.ok.wf htv]; exact htbody
  cases tv
  case sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv q4.ok.wf htv htbody
    obtain ⟨z, s8, k8, hz8⟩ := bindOk hz7
    obtain ⟨hs8, hz⟩ := zeroLevel_run (hpin.mono q4.ext q4.pins) k8
    rw [hs8] at hz8
    obtain ⟨v, s9, k9, hz9⟩ := bindOk hz8
    have p9 := lvlEq?_pstep q4.ok k9
    have q9 : PStep s₀ s9 := q4.trans p9
    have hprop : ∀ (μ : CheckMode) (env : Env) (fe : IFEnv), CheckOK μ env fe s₀ →
        v = Level.isEquiv l .zero := by
      intro μ env fe hc
      have hc4 := (q4.toCore hc).ok
      obtain ⟨-, -, -, lu, lv, hlu, hlv, ha⟩ :=
        AM.of_run (P := fun t => t = s4) rfl k9 (Core.lvlEq?_spec s4 u z hc4)
      rw [hl] at hlu; rw [hz] at hlv
      cases hlu; cases hlv; exact ha
    have g7 : (cvR.levelParams == cvT.levelParams) =
        (cvRP.levelParams == cvTP.levelParams) :=
      beq_nhandleList_eq q9.ok.wf (denoteNListE_ext q9.ext _ _ hRlps)
        (denoteNListE_ext q9.ext _ _ hlps)
    rw [g7] at hz9
    cases hlp : cvR.levelParams with
    | nil =>
      have hlpP : cvRP.levelParams = [] := by
        rw [hlp] at hRlps; simp [Frontend.denoteNList] at hRlps; exact hRlps
      rw [hlp] at hz9
      obtain ⟨y, s10, k10, hz10⟩ := bindOk hz9
      obtain ⟨rfl, rfl⟩ := pureOk k10
      obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz10
      obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
        (by intro c hc; simp [NNodeView.children] at hc) kA
      have hanon' : denoteN sA.store.ns anon = some ConLeche.Name.anonymous := by
        rw [hanon]; rfl
      have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
      obtain ⟨bA, sB, kB, hzB⟩ := bindOk hzA
      obtain ⟨pB, hbA⟩ := structShape_spec cvT.name cvC.name cvTP.name cvCP.name
        cvT.levelParams cvTP.levelParams anon .anonymous false nP nF cvT.type cvC.type
        cvR.type cvTP.type cvCP.type cvRP.type sA sB bA pA.ok
        ⟨denoteN_ext hT xA, denoteN_ext hC xA, denoteNListE_ext xA _ _ hlps, hanon',
          denote_ext hTty xA, denote_ext hCty xA, denote_ext hRty xA⟩ kB
      have hbA' : bA = ConLeche.structShape cvTP.name cvCP.name cvTP.levelParams
          .anonymous false nP nF cvTP.type cvCP.type cvRP.type := hbA
      have qB : PStep s₀ sB := (q9.trans pA).trans pB
      have xB : Ext s₀.store sB.store := qB.ext
      rw [hbA'] at hzB
      split at hzB
      case isTrue hc3 =>
        obtain ⟨rfl, rfl⟩ := pureOk hzB
        refine ⟨qB, ?_⟩
        simp only [hlpP]
        rw [hlpP] at hc3; rw [if_pos hc3]
        refine ⟨_, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT xB, cvC := denoteCV_ext hcvC xB, nP := rfl,
                nF := rfl, cvR := denoteCV_ext hcvR xB,
                elim := denoteN_ext hanon' pB.ext,
                resSort := denoteL_ext hl (p9.ext.trans (pA.ext.trans pB.ext)),
                rhs := denote_ext hrhs xB, large := rfl,
                isProp := by rw [hprop μ env fe hc] }
      case isFalse hc3 =>
        obtain ⟨rfl, rfl⟩ := pureOk hzB
        refine ⟨qB, ?_⟩
        show _ = none
        simp only [hlpP]
        rw [hlpP] at hc3; rw [if_neg hc3]
    | cons elim relps =>
      rw [hlp] at hRlps
      simp only [Frontend.denoteNList] at hRlps
      cases helim : denoteN s₀.store.ns elim with
      | none => rw [helim] at hRlps; simp at hRlps
      | some elimP =>
      cases hrel : Frontend.denoteNList s₀.store.ns relps with
      | none => rw [helim, hrel] at hRlps; simp at hRlps
      | some relpsP =>
      rw [helim, hrel] at hRlps
      have hlpP : cvRP.levelParams = elimP :: relpsP := (Option.some.inj hRlps).symm
      rw [hlp] at hz9
      obtain ⟨b, s10, k10, hz10⟩ := bindOk hz9
      obtain ⟨p10, hbv⟩ := structShape_spec cvT.name cvC.name cvTP.name cvCP.name
        cvT.levelParams cvTP.levelParams elim elimP true nP nF cvT.type cvC.type
        cvR.type cvTP.type cvCP.type cvRP.type s9 s10 b q9.ok
        ⟨denoteN_ext hT q9.ext, denoteN_ext hC q9.ext, denoteNListE_ext q9.ext _ _ hlps,
          denoteN_ext helim q9.ext, denote_ext hTty q9.ext, denote_ext hCty q9.ext,
          denote_ext hRty q9.ext⟩ k10
      have hbv' : b = ConLeche.structShape cvTP.name cvCP.name cvTP.levelParams
          elimP true nP nF cvTP.type cvCP.type cvRP.type := hbv
      have q10 : PStep s₀ s10 := q9.trans p10
      have g8 : (relps == cvT.levelParams) = (relpsP == cvTP.levelParams) :=
        beq_nhandleList_eq q10.ok.wf (denoteNListE_ext q10.ext _ _ hrel)
          (denoteNListE_ext q10.ext _ _ hlps)
      have g9 : cvT.levelParams.contains elim = cvTP.levelParams.contains elimP :=
        denoteNList_contains q10.ok.wf _ _ (denoteNListE_ext q10.ext _ _ hlps) _ _
          (denoteN_ext helim q10.ext)
      rw [hbv', g8, g9] at hz10
      split at hz10
      case isTrue hc2 =>
        obtain ⟨y, s11, k11, hz11⟩ := bindOk hz10
        obtain ⟨rfl, rfl⟩ := pureOk k11
        obtain ⟨rfl, rfl⟩ := pureOk hz11
        refine ⟨q10, ?_⟩
        simp only [hlpP]
        rw [if_pos hc2]
        refine ⟨_, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT q10.ext, cvC := denoteCV_ext hcvC q10.ext,
                nP := rfl, nF := rfl, cvR := denoteCV_ext hcvR q10.ext,
                elim := denoteN_ext helim q10.ext,
                resSort := denoteL_ext hl (p9.ext.trans p10.ext),
                rhs := denote_ext hrhs q10.ext, large := rfl,
                isProp := by rw [hprop μ env fe hc] }
      case isFalse hc2 =>
        obtain ⟨y, s11, k11, hz11⟩ := bindOk hz10
        obtain ⟨rfl, rfl⟩ := pureOk k11
        simp only [hlpP]
        rw [if_neg hc2]
        obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz11
        obtain ⟨pA, hanon⟩ := internNNode_run q10.ok
          (by intro c hc; simp [NNodeView.children] at hc) kA
        have hanon' : denoteN sA.store.ns anon = some ConLeche.Name.anonymous := by
          rw [hanon]; rfl
        have xA : Ext s₀.store sA.store := q10.ext.trans pA.ext
        obtain ⟨bA, sB, kB, hzB⟩ := bindOk hzA
        obtain ⟨pB, hbA⟩ := structShape_spec cvT.name cvC.name cvTP.name cvCP.name
          cvT.levelParams cvTP.levelParams anon .anonymous false nP nF cvT.type cvC.type
          cvR.type cvTP.type cvCP.type cvRP.type sA sB bA pA.ok
          ⟨denoteN_ext hT xA, denoteN_ext hC xA, denoteNListE_ext xA _ _ hlps, hanon',
            denote_ext hTty xA, denote_ext hCty xA, denote_ext hRty xA⟩ kB
        have hbA' : bA = ConLeche.structShape cvTP.name cvCP.name cvTP.levelParams
            .anonymous false nP nF cvTP.type cvCP.type cvRP.type := hbA
        have qB : PStep s₀ sB := (q10.trans pA).trans pB
        have xB : Ext s₀.store sB.store := qB.ext
        rw [hbA'] at hzB
        split at hzB
        case isTrue hc3 =>
          obtain ⟨rfl, rfl⟩ := pureOk hzB
          refine ⟨qB, ?_⟩
          rw [hlpP] at hc3; rw [if_pos hc3]
          refine ⟨_, rfl, fun μ env fe hc => ?_⟩
          exact { cvT := denoteCV_ext hcvT xB, cvC := denoteCV_ext hcvC xB, nP := rfl,
                  nF := rfl, cvR := denoteCV_ext hcvR xB,
                  elim := denoteN_ext hanon' pB.ext,
                  resSort := denoteL_ext hl (p9.ext.trans (p10.ext.trans (pA.ext.trans pB.ext))),
                  rhs := denote_ext hrhs xB, large := rfl,
                  isProp := by rw [hprop μ env fe hc] }
        case isFalse hc3 =>
          obtain ⟨rfl, rfl⟩ := pureOk hzB
          refine ⟨qB, ?_⟩
          show _ = none
          rw [hlpP] at hc3; rw [if_neg hc3]
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk hz7
     refine ⟨q4, ?_⟩
     have hns := ExprOps.denoteEView_not_sort htbv (by simp)
     show _ = none
     cases tbodyP <;> first | rfl | exact absurd rfl (hns _))

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
Recognise a direct simple-structure block.  `none` means "not this class", and
the relation is TWO-SIDED (`ROp`): a twin that failed to recognise a block
con-leche recognises would take the other route.

**CORE grade, not pure** (task #97-P3-Ind round 2's finding; the argument is
in `Bridge/Inductives/Rel.lean`'s frame section).  The recogniser reads the
former's result sort and asks `lvlEq? s z` for `isProp`.  `structShape` itself
is untouched and stays pure: the `lvlEq?` call is in `structPartsCore?`'s own
body.

**It stays here after task #97-P3-Frame.**  That task made `PStep`'s cache
clause true of a `lvlEq?` call, so the FRAME no longer forces the grade — but
`RSParts` carries `SPartsRel.isProp`, which is the verdict, and the verdict a
cache hit answers is `Level.isEquiv`'s only under `LvlEqCacheOK`.  `StateOK`
does not carry it, so the ANSWER forces the grade instead.

**CLOSED** (task #97-P3-Ind round 6): `structPartsCore?_run` at the
`CheckOK` it was handed — `CheckOK.pins` is the pin licence and the relation's
`CheckOK` hypothesis is this statement's own. -/
theorem structPartsCore?_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (ROp RSParts (ConLeche.structPartsCore? blockP)) := by
  intro s₀ s' r hok hb hrun
  obtain ⟨hstep, hrel⟩ :=
    structPartsCore?_run block blockP s₀ s' r hok.state hok.pins hb hrun
  exact ⟨hstep.toCore hok, hrel.mono (fun _ _ h => h μ env fe hok)⟩

/-! ## The recogniser's `isSome` half, for the parse

`Bridge/Frontend/ProjRec.lean`'s `projRecOwners_run` calls this recogniser and
`NativeParts.lean`'s, and **reads both through `.isSome` alone** — `isProp`
fills a field of a record the recogniser has already decided to return.  Its
own hypothesis is `StateOK`, far too weak for `structPartsCore?_spec`'s
`CSpec` (whose `SPartsRel.isProp` conjunct is `lvlEq?`'s verdict and needs
`LvlEqCacheOK`), so it cannot consume that statement at all.  This is the
statement it can: the `isSome` half, at the PURE grade.

**`PSpecP`, not `PSpec`** — the same finding as `structProjGuards_spec`'s, and
here the pin read is LOAD-BEARING for the answer rather than incidental:
`structPartsCore?` asks `reservedBasisNames` and tests `reserved.contains T`,
so the recognition verdict itself is wrong at a state whose pin table is
wrong.  The Frontend tier therefore needs `PinsOK` at its call site; the parse
runs after `internAllPins`, so it has it. -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329
structPartsCore? — **the recogniser's `isSome` half at the PURE grade**, for
`Bridge/Frontend/ProjRec.lean`'s `projRecOwners_run` (task #97-P3-Frontend's
sorry list, item 13, which names this lemma).  The `isProp` field — the one
thing that forces `structPartsCore?_spec` up to `CSpec` — is not mentioned, so
this statement lives at `StateOK` + `PinsOK` and the parse can use it.

**CLOSED** (task #97-P3-Ind round 6): the one dispatch lemma feeding both,
as round 3 intended — `structPartsCore?_run`, read through `ROp.isSome`, which
does not look at the relation at all. -/
theorem structPartsCore?_isSome (block : List IConstantInfo)
    (blockP : List ConstantInfo) :
    PSpecP (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (fun _ r => r.isSome = (ConLeche.structPartsCore? blockP).isSome) := by
  intro s₀ s' r hok hpin hb hrun
  obtain ⟨hstep, hrel⟩ := structPartsCore?_run block blockP s₀ s' r hok hpin hb hrun
  exact ⟨hstep, hrel.isSome⟩

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
**The one arithmetic identification of this module**: con-leche writes the
projection parameter spine as `bvar (nP - k)` and `structPsAt 1 nP` as
`bvar (1 + nP - 1 - k)`.  The arena's `structProjPs` is `structPsAt 1 nP` by
definition (task #97d-2 kept the twin's two names apart because con-leche
writes them at different frames), so the twins agree exactly when these two
`Nat` expressions do — which they do, and `omega` says so. -/
theorem structProjPs_eq (nP : Nat) :
    ConLeche.structPsAt 1 nP = ConLeche.structProjPs nP := by
  simp only [ConLeche.structPsAt, ConLeche.structProjPs]
  congr 1
  funext k
  congr 1
  omega

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
The projection types' parameter spine. -/
theorem structProjPs_spec (nP : Nat) :
    PSpec PT (Arena.structProjPs nP) (REL (ConLeche.structProjPs nP)) := by
  rw [← structProjPs_eq]
  exact structPsAt_spec 1 nP

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:339-345 structProjArgP
The `j`-th projection applied to the structure variable.

**CLOSED** (task #97-P3-Ind round 2): `internBVarE_run` then
`internProjE_run`. -/
theorem structProjArgP_spec (T : NIdx) (TP : ConLeche.Name) (j : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP)
      (Arena.structProjArgP T j) (RE (ConLeche.structProjArgP TP j)) := by
  intro s₀ s' r hok hT hrun
  simp only [Arena.structProjArgP] at hrun
  obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hb⟩ := internBVarE_run hok h1
  obtain ⟨hstep2, hr⟩ :=
    internProjE_run hstep1.ok (denoteN_ext hT hstep1.ext) hb h2
  exact ⟨hstep1.trans hstep2, hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift — the run
form of `Bridge/ExprOps/Subst.lean`'s closed `instPisAtLift_spec` at this
tier's frame, with the answer as an `ROp RE`. -/
theorem instPisAtLift_pstep {fuel : Nat} {args : List EIdx} {argsP : List Expr}
    {s₀ s' : AState} {c : EIdx} {cP : Expr} {r : Option EIdx}
    (hok : StateOK s₀) (ha : Frontend.denoteEList s₀.store args = some argsP)
    (hc : denoteE s₀.store c = some cP)
    (hrun : Arena.instPisAtLift fuel args c s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ ROp RE (Expr.instPisAtLift argsP cP) s'.store r := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.instPisAtLift_spec fuel args s₀ c hok (by rw [ha]; rfl) (by rw [hc]; rfl))
  refine ⟨PStep.of_caches h1 h2 h3 h4 h5, ?_⟩
  have h7 := h6 argsP ha cP hc
  cases r with
  | none => simp only [denoteEO, Option.some.injEq] at h7; exact h7.symm
  | some j =>
    simp only [denoteEO, Option.map_eq_some_iff] at h7
    obtain ⟨e, he, hx⟩ := h7
    exact ⟨e, hx.symm, he⟩

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:347-354 structProjResidP
The constructor type's residual after `i` projections have been substituted.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem structProjResidP_spec (T : NIdx) (TP : ConLeche.Name) (nP : Nat)
    (cty : EIdx) (ctyP : Expr) (i : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjResidP T nP cty i)
      (ROp RE (ConLeche.structProjResidP TP nP ctyP i)) := by
  induction i with
  | zero =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨_, hc⟩ := hpre
    simp only [Arena.structProjResidP] at hrun
    obtain ⟨ps, s1, k1, hz1⟩ := bindOk hrun
    obtain ⟨p1, hps⟩ := structProjPs_spec nP s₀ s1 ps hok trivial k1
    obtain ⟨p2, hr⟩ := instPisAtLift_pstep p1.ok hps (denote_ext hc p1.ext) hz1
    exact ⟨p1.trans p2, hr⟩
  | succ i ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hT, hc⟩ := hpre
    simp only [Arena.structProjResidP] at hrun
    obtain ⟨o, s1, k1, hz1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := ih s₀ s1 o hok ⟨hT, hc⟩ k1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk hz1
      refine ⟨p1, ?_⟩
      show ConLeche.structProjResidP TP nP ctyP (i + 1) = none
      simp only [ConLeche.structProjResidP, show ConLeche.structProjResidP TP nP ctyP i = none
        from ho, Option.bind_none]
    | some h =>
      obtain ⟨e, he, hd⟩ := ho
      obtain ⟨a, s2, k2, hz2⟩ := bindOk hz1
      obtain ⟨p2, ha⟩ := structProjArgP_spec T TP i s1 s2 a p1.ok
        (denoteN_ext hT p1.ext) k2
      obtain ⟨p3, hr⟩ := instPisAtLift_pstep (argsP := [ConLeche.structProjArgP TP i])
        p2.ok (by simp only [Frontend.denoteEList, ha]) (denote_ext hd p2.ext) hz2
      refine ⟨p1.trans (p2.trans p3), ?_⟩
      simp only [ConLeche.structProjResidP, he, Option.bind_some]
      exact hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1577 bvarB_eq — **the cutoff's
run form**, at this tier's frame: `Bridge/ExprOps/Ranges.lean`'s `bvarB_run`
answers `Expr.bvarB` and moves nothing but the `bvarBound` memo, which
`PStep` does not frame. -/
theorem bvarB_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr}
    {r : Nat} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.bvarB fuel e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ s'.store = s₀.store ∧ r = Expr.bvarB eP := by
  obtain ⟨h1, h2, h3, _, h5⟩ :=
    ExprOps.bvarB_run hok (by rw [hd]; rfl) hrun
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ ?_ h2 h3, h1, h5 eP hd⟩
  · rw [h1]; exact Ext.refl _
  · rw [h1]; exact BMExt.refl _

/-! ## `hasLooseBVarB`, memoised

`hasLooseBVarBIns` has NO statement of its own: it is the memo-insert helper
(con-leche's `Expr.hasLooseBVarBIns`), a pure function on `Bool ×
Std.HashMap` with no handle in it, and its content is entirely inside
`hasLooseBVarBGo_spec`'s invariant step.  Census class (S). -/

/-! ### The pure side's own equations

`Expr.hasLooseBVarB` is `if e.bvarB ≤ i then false else <the ten-way walk>`,
so every arm of the twin's dispatch needs the same two-step unfolding.  These
are con-leche's `hasLooseBVarB_eq` proof's first line, once per shape. -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:378-390 (the `if`)
— **the cutoff's own fact**: a node whose loose-bvar bound is at or below `i`
has no `bvar i`.  This is what the twin's early return computes. -/
theorem hasLooseBVarB_cut {i : Nat} {e : Expr} (hc : e.bvarB ≤ i) :
    Expr.hasLooseBVarB i e = false := by
  cases e <;> (rw [Expr.hasLooseBVarB]; exact if_pos hc)

theorem hasLooseBVarB_bvar {i j : Nat} (hc : ¬ (Expr.bvar j).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.bvar j) = (i == j) := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

theorem hasLooseBVarB_app {i : Nat} {f a : Expr}
    (hc : ¬ (Expr.app f a).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.app f a) =
      (Expr.hasLooseBVarB i f || Expr.hasLooseBVarB i a) := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

theorem hasLooseBVarB_lam {i : Nat} {ty b : Expr} {m : BinderMeta}
    (hc : ¬ (Expr.lam ty b m).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.lam ty b m) =
      (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

theorem hasLooseBVarB_forallE {i : Nat} {ty b : Expr} {m : BinderMeta}
    (hc : ¬ (Expr.forallE ty b m).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.forallE ty b m) =
      (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

theorem hasLooseBVarB_letE {i : Nat} {t v b : Expr}
    (hc : ¬ (Expr.letE t v b).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.letE t v b) =
      (Expr.hasLooseBVarB i t || Expr.hasLooseBVarB i v ||
        Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

theorem hasLooseBVarB_proj {i : Nat} {n : ConLeche.Name} {k : Nat} {e : Expr}
    (hc : ¬ (Expr.proj n k e).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.proj n k e) = Expr.hasLooseBVarB i e := by
  rw [Expr.hasLooseBVarB]; exact if_neg hc

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
The memoised walk: the answer is the real one AND the memo it hands back is
still sound.

**CLOSED** (task #97-P3-Ind round 3): a fuel induction generalising the memo,
the cursor and the handle, with the ten-way `view` dispatch as its arm.  The
memo travels as a HYPOTHESIS (`LooseMemoOK`) and comes back as a CONCLUSION,
so a hit is discharged by the invariant itself (`hit`) and a miss by
`LooseMemoOK.insert` (`fin`); the early return is
`Bridge/ExprOps/Ranges.lean`'s `bvarB_run` (closed) read through
`bvarB_pstep` plus `hasLooseBVarB_cut`. -/
theorem hasLooseBVarBGo_spec (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ LooseMemoOK memo st)
      (Arena.hasLooseBVarBGo memo i fuel h)
      (fun st r => r.1 = Expr.hasLooseBVarB i hP ∧ LooseMemoOK r.2 st) := by
  induction fuel generalizing memo i h hP with
  | zero =>
    intro s₀ s' r hok hp hrun
    simp only [Arena.hasLooseBVarBGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hd, hm⟩ := hp
    simp only [Arena.hasLooseBVarBGo] at hrun
    obtain ⟨bb, s₁, hb, h2⟩ := bindOk hrun
    obtain ⟨hstep0, hst0, rfl⟩ := bvarB_pstep hok hd hb
    have hok1 : StateOK s₁ := hstep0.ok
    have hd1 : denoteE s₁.store h = some hP := by rw [hst0]; exact hd
    have hm1 : LooseMemoOK memo s₁.store := by rw [hst0]; exact hm
    -- the shared tail: record the answer in the memo and stop
    have fin : ∀ {s₂ s₃ : AState} {y r' : Bool × Std.HashMap (EIdx × Nat) Bool},
        PStep s₁ s₂ → y.1 = Expr.hasLooseBVarB i hP →
        LooseMemoOK y.2 s₂.store →
        (pure (Arena.hasLooseBVarBIns h i y) :
            AM (Bool × Std.HashMap (EIdx × Nat) Bool)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.hasLooseBVarB i hP ∧
          LooseMemoOK r'.2 s₃.store := by
      intro s₂ s₃ y r' hs hy hmy hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hstep0.trans hs, hy,
        LooseMemoOK.insert hmy (denote_ext hd1 hs.ext) hy⟩
    -- the shared memo HIT: the invariant is exactly what makes it sound
    have hit : ∀ {s₃ : AState} {r₀ : Bool}
        {r' : Bool × Std.HashMap (EIdx × Nat) Bool},
        memo[(h, i)]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap (EIdx × Nat) Bool) :
            AM (Bool × Std.HashMap (EIdx × Nat) Bool)) s₁ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.hasLooseBVarB i hP ∧
          LooseMemoOK r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm1 (h, i) r₀ hlk
      obtain rfl := Option.some.inj (hd1.symm.trans he)
      exact ⟨hstep0, hre, hm1⟩
    split at h2
    · -- the packed-bound cutoff
      rename_i hc
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨hstep0, (hasLooseBVarB_cut hc).symm, hm1⟩
    · rename_i hc
      obtain ⟨v, s₂, hv, h3⟩ := bindOk h2
      obtain ⟨rfl, hw⟩ := view_run hv
      cases v
      case bvar j =>
        obtain ⟨rfl, rfl⟩ := pureOk h3
        obtain rfl := denote_bvar_inv hok1.wf hw hd1
        exact ⟨hstep0, (hasLooseBVarB_bvar hc).symm, hm1⟩
      case fvar k ty =>
        obtain ⟨rfl, rfl⟩ := pureOk h3
        obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case sort u =>
        obtain ⟨rfl, rfl⟩ := pureOk h3
        obtain ⟨l, rfl, _⟩ := denote_sort_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case const n us =>
        obtain ⟨rfl, rfl⟩ := pureOk h3
        obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case lit l =>
        obtain ⟨rfl, rfl⟩ := pureOk h3
        obtain rfl := denote_lit_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case app f a =>
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := bindOk h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i f ef _ _ (b1, m1) hok1 ⟨hf, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i ef := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := bindOk h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 i a ea _ _ (b2, m2) hsA.ok
                ⟨denote_ext ha hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB i ea := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_app hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := bindOk h4
            obtain ⟨rfl, rfl⟩ := pureOk hy
            exact fin hsA (by simp [hasLooseBVarB_app hc, ← hrA']) hmA hz
      case lam ty b m =>
        obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := bindOk h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i ty et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := bindOk h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 (i + 1) b eb _ _ (b2, m2) hsA.ok
                ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB (i + 1) eb := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_lam hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := bindOk h4
            obtain ⟨rfl, rfl⟩ := pureOk hy
            exact fin hsA (by simp [hasLooseBVarB_lam hc, ← hrA']) hmA hz
      case forallE ty b m =>
        obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := bindOk h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i ty et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := bindOk h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 (i + 1) b eb _ _ (b2, m2) hsA.ok
                ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB (i + 1) eb := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_forallE hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := bindOk h4
            obtain ⟨rfl, rfl⟩ := pureOk hy
            exact fin hsA (by simp [hasLooseBVarB_forallE hc, ← hrA']) hmA hz
      case letE lt lv lb =>
        obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ :=
          denote_letE_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := bindOk h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i lt et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, h5⟩ := bindOk h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 i lv ev _ _ (b2, m2) hsA.ok
                ⟨denote_ext hval hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB i ev := hrB
            cases b2
            · obtain ⟨p3, s₄, hc3, hz⟩ := bindOk h5
              obtain ⟨b3, m3⟩ := p3
              obtain ⟨hsC, hrC, hmC⟩ :=
                ih m2 (i + 1) lb eb _ _ (b3, m3) hsB.ok
                  ⟨denote_ext (denote_ext hbd hsA.ext) hsB.ext, hmB⟩ hc3
              have hrC' : b3 = Expr.hasLooseBVarB (i + 1) eb := hrC
              exact fin ((hsA.trans hsB).trans hsC)
                (by simp [hasLooseBVarB_letE hc, ← hrA', ← hrB', ← hrC'])
                hmC hz
            · obtain ⟨y, s₃', hy, hz⟩ := bindOk h5
              obtain ⟨rfl, rfl⟩ := pureOk hy
              exact fin (hsA.trans hsB)
                (by simp [hasLooseBVarB_letE hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := bindOk h4
            obtain ⟨rfl, rfl⟩ := pureOk hy
            exact fin hsA (by simp [hasLooseBVarB_letE hc, ← hrA']) hmA hz
      case proj pn pk psub =>
        obtain ⟨nm, es, rfl, _, hsub⟩ := denote_proj_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, hz⟩ := bindOk h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i psub es _ _ (b1, m1) hok1 ⟨hsub, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i es := hrA
          exact fin hsA (by simp [hasLooseBVarB_proj hc, ← hrA']) hmA hz

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:624-626 Expr.hasLooseBVarBFast
The entry: an empty memo is sound, so the answer is the real one.

**CLOSED** (task #97-P3-Ind round 3): `hasLooseBVarBGo_spec` at the empty
memo, which `LooseMemoOK.empty` says is sound. -/
theorem hasLooseBVarBFast_spec (i : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.hasLooseBVarBFast i e) (RV (Expr.hasLooseBVarB i eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.hasLooseBVarBFast] at hrun
  obtain ⟨p, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ :=
    hasLooseBVarBGo_spec ∅ i Arena.coreWalkFuel e eP s₀ s₁ p hok
      ⟨hd, LooseMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

/-! ### `stripPis`, in run form — MOVED to `Bridge/Inductives/Rel.lean`

`stripPis_pstep`, `stripPis_none` and `stripPis_some` are in `Rel.lean` beside
`denoteBP_someB` since task #97-P3-Ind round 5: `structShape_spec` sits ABOVE
this point in the file (con-leche's source order puts it at
`StructParts.lean:246`) and needs them, and `Rel.lean` is already where this
tier keeps the `ExprOps` readers it borrows (`getAppFn_run`, `getAppArgs_run`,
`fvarTypeD_run`, `piSortTeleLen?_spec`).  `ConRon.Bridge.Inductives` is the
same namespace, so every use below reads unchanged. -/

/-! ## The projection guards -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:633-641 structUsedLater
Is field `j` mentioned by a later field's domain?

**CLOSED** (task #97-P3-Ind round 3): `hasLooseBVarBFast_spec` under the
constructor type's telescope, with `stripPis_pstep`'s two inversions for the
dispatch. -/
theorem structUsedLater_spec (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structUsedLater cty nP j)
      (RV (ConLeche.structUsedLater ctyP nP j)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.structUsedLater] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  show PStep s₀ s' ∧ r = ConLeche.structUsedLater ctyP nP j
  rw [ConLeche.structUsedLater]
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    rw [stripPis_none hbp]
    exact ⟨PStep.refl hok, rfl⟩
  | some p =>
    obtain ⟨bs, rest⟩ := p
    obtain ⟨xs, x, hsp, hx⟩ := stripPis_some hbp
    rw [hsp]
    exact hasLooseBVarBFast_spec 0 rest x _ _ r hok hx h2

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:669-674 structUsedLaterGo
The same with the memo threaded (task #236's one shared memo across `nF`
calls).

**CLOSED** (task #97-P3-Ind round 3): `hasLooseBVarBGo_spec` under the
telescope, the memo travelling verbatim through the `none` arm. -/
theorem structUsedLaterGo_spec (memo : Std.HashMap (EIdx × Nat) Bool)
    (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterGo memo cty nP j)
      (fun st r => r.1 = ConLeche.structUsedLater ctyP nP j ∧
        LooseMemoOK r.2 st) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hd, hm⟩ := hp
  simp only [Arena.structUsedLaterGo] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  show PStep s₀ s' ∧ r.1 = ConLeche.structUsedLater ctyP nP j ∧
    LooseMemoOK r.2 s'.store
  rw [ConLeche.structUsedLater]
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    rw [stripPis_none hbp]
    exact ⟨PStep.refl hok, rfl, hm⟩
  | some p =>
    obtain ⟨bs, rest⟩ := p
    obtain ⟨xs, x, hsp, hx⟩ := stripPis_some hbp
    rw [hsp]
    exact hasLooseBVarBGo_spec memo 0 Arena.coreWalkFuel rest x _ _ r hok
      ⟨hx, hm⟩ h2

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:685-692 structUsedLaterList
The `n` answers from `base` up, one memo through all of them.

**CLOSED** (task #97-P3-Ind round 3): a `Nat` recursion over
`structUsedLaterGo_spec`, generalising the memo AND the base.  Stronger than
con-leche's own `structUsedLaterList_spec`, which says only what the `t`-th
entry is: here the LIST is named, which is what `structProjGuards_spec`'s
fold needs. -/
theorem structUsedLaterList_spec (cty : EIdx) (ctyP : Expr) (nP : Nat)
    (memo : Std.HashMap (EIdx × Nat) Bool) (n base : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterList cty nP memo n base)
      (RV ((List.range n).map fun k => ConLeche.structUsedLater ctyP nP (base + k))) := by
  induction n generalizing memo base with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.structUsedLaterList] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simp⟩
  | succ n ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hd, hm⟩ := hp
    simp only [Arena.structUsedLaterList] at hrun
    obtain ⟨p, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hsA, hrA, hmA⟩ :=
      structUsedLaterGo_spec memo cty ctyP nP base _ _ p hok ⟨hd, hm⟩ h1
    obtain ⟨rest, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨hsB, hrB⟩ :=
      ih p.2 (base + 1) _ _ rest hsA.ok ⟨denote_ext hd hsA.ext, hmA⟩ h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨hsA.trans hsB, ?_⟩
    show p.1 :: rest = _
    rw [hrA, hrB, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
    congr 1
    exact List.map_congr_left (fun k _ => by congr 1; omega)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656
structProjGuards — **the guard list has one entry per field**, by
construction: the pure function is a `List.range nF` map.  This is the fact
`Bridge/StateOK.lean`'s `IProjTableOK.guards` asks of the table
`checkStructProjTable` pushes, and `checkStructProjTable_spec`'s hypothesis
`hg` is where it has to arrive (`Bridge/Checker/Inv.lean`'s
`projTableOK_of_install` names the same hypothesis).  The chain is
`structProjGuards_spec` (the handle list denotes the pure one) plus
`denoteLList_length` (a denotation keeps its length) plus this. -/
theorem structProjGuards_length (cty : Expr) (nP nF : Nat)
    (sorts : List Level) :
    (ConLeche.structProjGuards cty nP nF sorts).length = nF := by
  simp only [ConLeche.structProjGuards, List.length_map, List.length_range]

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
The guard level of each field: `Prop` where the field is used later, the
field's own sort otherwise.  The answer is a `List LIdx` and NOT an `LsIdx`
(task #97d-2's deviation 6), so the relation is `RLL`.

**CLOSED** (task #97-P3-Ind round 3), and **at `PSpecP`, not `PSpec`** —
round 3's finding, the campaign's sixth statement defect.  The twin opens with
`let z ← zeroLevel`, a PIN READ, and `PSpec`'s precondition is a predicate on
the STORE: it cannot say what `s.pins.zeroLevel` denotes, and
`Arena/Pins.lean`'s `pinsReady` tests only the name array's SIZE.  At a state
whose `pins.zeroLevel` denotes `.param foo` the run accepts and answers
something else — take `sorts = []`, `sortsP = []`, `nF = 1`, where the
statement reduces to exactly `denoteL st.ls z = some .zero`.  `PinsOK` is the
missing licence and `PSpecP` is the shape that carries it; this is the only
twin of the tier under a `PSpec` that reads the pin table (the other four pin
readers — `withSort`, `structPartsCore?`, `nativeShape?`, `checkSumCtor` —
are already at `CSpec`, which has `CheckOK.pins`).

The proof: `structUsedLaterList_spec` for the answer table, then the two
`let rec`s by their own inductions — `col` over `List.range' j k` and `row`
over `List.range' i k`, the guard `j < nF` travelling as `j + k ≤ nF`. -/
theorem structProjGuards_spec (cty : EIdx) (ctyP : Expr) (nP nF : Nat)
    (sorts : List LIdx) (sortsP : List Level) :
    PSpecP (fun st => denoteE st cty = some ctyP ∧
        denoteLList st.ls sorts = some sortsP)
      (Arena.structProjGuards cty nP nF sorts)
      (RLL (ConLeche.structProjGuards ctyP nP nF sortsP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hd, hs⟩ := hp
  simp only [Arena.structProjGuards] at hrun
  obtain ⟨z, s₁, hz, h2⟩ := bindOk hrun
  obtain ⟨rfl, hzd⟩ := zeroLevel_run hpins hz
  obtain ⟨used, s₂, hu, h3⟩ := bindOk h2
  obtain ⟨hsU, hrU⟩ :=
    structUsedLaterList_spec cty ctyP nP ∅ nF 0 _ _ used hok
      ⟨hd, LooseMemoOK.empty⟩ hu
  -- the answer table reads back, entry by entry
  have hused : ∀ m, m < nF →
      used.getD m false = ConLeche.structUsedLater ctyP nP m := by
    intro m hm
    rw [show used = _ from hrU, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hm]
    simp
  -- `col`: the inner fold, over `List.range' j k`
  have hcol : ∀ (k j : Nat) (acc : LIdx) (accP : Level) (sa sb : AState)
      (rr : LIdx), StateOK sa →
      denoteLList sa.store.ls sorts = some sortsP →
      denoteL sa.store.ls z = some .zero →
      denoteL sa.store.ls acc = some accP → j + k ≤ nF →
      Arena.structProjGuards.col sorts z used j k acc sa = .ok (rr, sb) →
      PStep sa sb ∧ denoteL sb.store.ls rr =
        some ((List.range' j k).foldl (fun a m =>
          if ConLeche.structUsedLater ctyP nP m then
            Level.max a (sortsP.getD m .zero) else a) accP) := by
    intro k
    induction k with
    | zero =>
      intro j acc accP sa sb rr hoka _ _ hacc _ hr
      simp only [Arena.structProjGuards.col] at hr
      obtain ⟨rfl, rfl⟩ := pureOk hr
      exact ⟨PStep.refl hoka, by simpa using hacc⟩
    | succ k ih =>
      intro j acc accP sa sb rr hoka hsa hza hacc hle hr
      have hjn : j < nF := by omega
      simp only [Arena.structProjGuards.col] at hr
      rw [List.range'_succ]
      simp only [List.foldl_cons, Nat.add_one]
      rw [hused j hjn] at hr
      split at hr
      · rename_i hcond
        rw [if_pos hcond]
        obtain ⟨m, sm, hm, hr'⟩ := bindOk hr
        obtain ⟨hstepM, hmd⟩ :=
          internMaxL_run hoka hacc (denoteLList_getD hsa hza j) hm
        obtain ⟨hstepR, hrd⟩ :=
          ih (j + 1) m _ sm sb rr hstepM.ok
            (denoteLList_ext hstepM.ext.lss.ls _ _ hsa) (denoteL_ext hza hstepM.ext)
            hmd (by omega) hr'
        exact ⟨hstepM.trans hstepR, hrd⟩
      · rename_i hcond
        rw [if_neg hcond]
        exact ih (j + 1) acc accP sa sb rr hoka hsa hza hacc (by omega) hr
  -- `row`: the outer map, over `List.range' i k`
  have hrow : ∀ (k i : Nat) (sa sb : AState) (rr : List LIdx), StateOK sa →
      denoteLList sa.store.ls sorts = some sortsP →
      denoteL sa.store.ls z = some .zero → i + k ≤ nF →
      Arena.structProjGuards.row sorts z used i k sa = .ok (rr, sb) →
      PStep sa sb ∧ denoteLList sb.store.ls rr =
        some ((List.range' i k).map fun m =>
          (List.range m).foldl (fun a n =>
            if ConLeche.structUsedLater ctyP nP n then
              Level.max a (sortsP.getD n .zero) else a) (sortsP.getD m .zero)) := by
    intro k
    induction k with
    | zero =>
      intro i sa sb rr hoka _ _ _ hr
      simp only [Arena.structProjGuards.row] at hr
      obtain ⟨rfl, rfl⟩ := pureOk hr
      exact ⟨PStep.refl hoka, by simp [denoteLList]⟩
    | succ k ih =>
      intro i sa sb rr hoka hsa hza hle hr
      simp only [Arena.structProjGuards.row] at hr
      obtain ⟨g, sg, hg, hr1⟩ := bindOk hr
      obtain ⟨hstepG, hgd⟩ :=
        hcol i 0 (sorts.getD i z) (sortsP.getD i .zero) sa sg g hoka hsa hza
          (denoteLList_getD hsa hza i) (by omega) hg
      obtain ⟨rest, sr, hrest, hr2⟩ := bindOk hr1
      obtain ⟨hstepR, hrd⟩ :=
        ih (i + 1) sg sr rest hstepG.ok (denoteLList_ext hstepG.ext.lss.ls _ _ hsa)
          (denoteL_ext hza hstepG.ext) (by omega) hrest
      obtain ⟨rfl, rfl⟩ := pureOk hr2
      refine ⟨hstepG.trans hstepR, ?_⟩
      rw [List.range'_succ]
      simp only [List.map_cons, Nat.add_one]
      simp only [denoteLList, opt2, denoteL_ext hgd hstepR.ext, hrd,
        ← List.range_eq_range']
  obtain ⟨hstepRow, hrowd⟩ :=
    hrow nF 0 _ _ r hsU.ok (denoteLList_ext hsU.ext.lss.ls _ _ hs)
      (denoteL_ext hzd hsU.ext) (by omega) h3
  refine ⟨hsU.trans hstepRow, ?_⟩
  show denoteLList s'.store.ls r = some _
  rw [hrowd, ConLeche.structProjGuards, ← List.range_eq_range']

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:748-766 structProjBodiesGo
Peel `k` field binders, substituting the projection of the structure variable
for each.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem structProjBodiesGo_spec (T : NIdx) (TP : ConLeche.Name) (k i : Nat)
    (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP)
      (Arena.structProjBodiesGo T k i h)
      (ROp REL (ConLeche.structProjBodiesGo TP k i hP)) := by
  induction k generalizing i h hP with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.structProjBodiesGo] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], by simp only [ConLeche.structProjBodiesGo], rfl⟩
  | succ k ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hT, hh⟩ := hpre
    simp only [Arena.structProjBodiesGo] at hrun
    obtain ⟨v, s1, k1, hz1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at hz1
    have hhv : denoteEView s₀.store v = some hP := by
      rw [← denoteE_view_eq hok.wf hv]; exact hh
    split at hz1
    case h_1 fdom body m =>
      obtain ⟨fdomP, bodyP, rfl, hfd, hbd⟩ := denote_forallE_inv hok.wf hv hh
      obtain ⟨a, s2, k2, hz2⟩ := bindOk hz1
      obtain ⟨p2, ha⟩ := structProjArgP_spec T TP i s₀ s2 a hok hT k2
      obtain ⟨b, s3, k3, hz3⟩ := bindOk hz2
      obtain ⟨hok3, hx3, hbm3, hc3, hp3, -, hb⟩ :=
        ExprOps.instantiate1LiftFast_run p2.ok ha
          (by rw [denote_ext hbd p2.ext]; rfl) k3
      have p3 : PStep s2 s3 := PStep.of_caches hok3 hx3 hbm3 hc3 hp3
      have hb' := hb bodyP (denote_ext hbd p2.ext)
      obtain ⟨o, s4, k4, hz4⟩ := bindOk hz3
      obtain ⟨p4, ho⟩ := ih (i + 1) b _ s3 s4 o p3.ok
        ⟨denoteN_ext hT (p2.ext.trans p3.ext), hb'⟩ k4
      have q4 : PStep s₀ s4 := p2.trans (p3.trans p4)
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk hz4
        refine ⟨q4, ?_⟩
        show ConLeche.structProjBodiesGo TP (k + 1) i (.forallE fdomP bodyP m) = none
        simp only [ConLeche.structProjBodiesGo]
        rw [show ConLeche.structProjBodiesGo TP k (i + 1) _ = none from ho]
        rfl
      | some l =>
        obtain ⟨lP, hl, hdl⟩ := ho
        obtain ⟨rfl, rfl⟩ := pureOk hz4
        refine ⟨q4, fdomP :: lP, ?_, ?_⟩
        · simp only [ConLeche.structProjBodiesGo]
          rw [hl]; rfl
        · show Frontend.denoteEList _ (fdom :: l) = some (fdomP :: lP)
          simp only [Frontend.denoteEList, denote_ext hfd q4.ext, hdl]
    case h_2 hne =>
      obtain ⟨rfl, rfl⟩ := pureOk hz1
      refine ⟨PStep.refl hok, ?_⟩
      have hns := ExprOps.denoteEView_not_forallE hhv hne
      show _ = none
      cases hP <;> first | rfl | exact absurd rfl (hns _ _ _)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:768-771 structProjBodies
The entry, after `nP` parameter binders.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem structProjBodies_spec (T : NIdx) (TP : ConLeche.Name) (nP nF : Nat)
    (cty : EIdx) (ctyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjBodies T nP nF cty)
      (ROp REA (ConLeche.structProjBodies TP nP nF ctyP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hc⟩ := hpre
  simp only [Arena.structProjBodies] at hrun
  obtain ⟨ps, s1, k1, hz1⟩ := bindOk hrun
  obtain ⟨p1, hps⟩ := structProjPs_spec nP s₀ s1 ps hok trivial k1
  obtain ⟨o, s2, k2, hz2⟩ := bindOk hz1
  obtain ⟨p2, ho⟩ := instPisAtLift_pstep p1.ok hps (denote_ext hc p1.ext) k2
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk hz2
    refine ⟨p1.trans p2, ?_⟩
    show ConLeche.structProjBodies TP nP nF ctyP = none
    simp only [ConLeche.structProjBodies]
    rw [show Expr.instPisAtLift (ConLeche.structProjPs nP) ctyP = none from ho]
  | some h =>
    obtain ⟨e, he, hd⟩ := ho
    obtain ⟨o2, s3, k3, hz3⟩ := bindOk hz2
    obtain ⟨p3, ho2⟩ := structProjBodiesGo_spec T TP nF 0 h e s2 s3 o2 p2.ok
      ⟨denoteN_ext hT (p1.ext.trans p2.ext), hd⟩ k3
    have q3 : PStep s₀ s3 := p1.trans (p2.trans p3)
    cases o2 with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk hz3
      refine ⟨q3, ?_⟩
      show ConLeche.structProjBodies TP nP nF ctyP = none
      simp only [ConLeche.structProjBodies, he]
      rw [show ConLeche.structProjBodiesGo TP nF 0 e = none from ho2]
      rfl
    | some l =>
      obtain ⟨lP, hl, hdl⟩ := ho2
      obtain ⟨rfl, rfl⟩ := pureOk hz3
      refine ⟨q3, lP.toArray, ?_, ?_⟩
      · simp only [ConLeche.structProjBodies, he, hl]; rfl
      · show Frontend.denoteEArray _ l.toArray = _
        simp only [Frontend.denoteEArray, hdl]

/-! ## `mentionsConst`, memoised -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
The memoised walk.  Note the `fvar` arm: a free variable carries its type, and
the walk descends into it — DESIGN §8.3's "a handle determines its own typing
context".

**CLOSED** (task #97-P3-Ind round 3): the same fuel induction as
`hasLooseBVarBGo_spec`, without the cutoff — `mentionsConst` has no packed
bound to stop at.  The `.const` and `.proj` arms RETURN a handle comparison,
so they need `beq_handle_eq` (`Bridge/Inductives/Rel.lean`) at both signs, and
its `false` half is `denoteN_inj`: DESIGN §8.3's soundness obligation, cashed
here twice. -/
theorem mentionsConstGo_spec (T : NIdx) (TP : ConLeche.Name)
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        MentionsMemoOK TP memo st)
      (Arena.mentionsConstGo T memo fuel h)
      (fun st r => r.1 = Expr.mentionsConst TP hP ∧
        MentionsMemoOK TP r.2 st) := by
  induction fuel generalizing memo h hP with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.mentionsConstGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hT, hd, hm⟩ := hp
    simp only [Arena.mentionsConstGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    -- the shared tail: record the answer in the memo and stop
    have fin : ∀ {s₂ s₃ : AState} {b : Bool} {mm : Std.HashMap EIdx Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        PStep s₀ s₂ → b = Expr.mentionsConst TP hP →
        MentionsMemoOK TP mm s₂.store →
        (pure ((b, mm.insert h b) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsConst TP hP ∧
          MentionsMemoOK TP r'.2 s₃.store := by
      intro s₂ s₃ b mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, MentionsMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    -- the shared memo HIT
    have hit : ∀ {s₃ : AState} {r₀ : Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsConst TP hP ∧
          MentionsMemoOK TP r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, hn, _⟩ := denote_const_inv hok.wf hw hd
      refine ⟨PStep.refl hok, ?_, hm⟩
      simp only [Expr.mentionsConst]
      exact beq_handle_eq hok.wf hn hT
    case fvar k ty =>
      obtain ⟨t, rfl, hty⟩ := denote_fvar_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p, s₂, hin, hz⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo ty t _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hin
        have hrA' : b1 = Expr.mentionsConst TP t := hrA
        exact fin hsA (by simp only [Expr.mentionsConst]; exact hrA') hmA hz
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo f ef _ _ (b1, m1) hok ⟨hT, hf, hm⟩ hc1
        have hrA' : b1 = Expr.mentionsConst TP ef := hrA
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ :=
          ih m1 a ea _ _ (b2, m2) hsA.ok
            ⟨denoteN_ext hT hsA.ext, denote_ext ha hsA.ext, hmA⟩ hc2
        have hrB' : b2 = Expr.mentionsConst TP ea := hrB
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only [Expr.mentionsConst]; rw [hrA', hrB']) hmB hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        have hrA' : b1 = Expr.mentionsConst TP et := hrA
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ :=
          ih m1 b eb _ _ (b2, m2) hsA.ok
            ⟨denoteN_ext hT hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        have hrB' : b2 = Expr.mentionsConst TP eb := hrB
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only [Expr.mentionsConst]; rw [hrA', hrB']) hmB hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        have hrA' : b1 = Expr.mentionsConst TP et := hrA
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ :=
          ih m1 b eb _ _ (b2, m2) hsA.ok
            ⟨denoteN_ext hT hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        have hrB' : b2 = Expr.mentionsConst TP eb := hrB
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only [Expr.mentionsConst]; rw [hrA', hrB']) hmB hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ :=
        denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo lt et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        have hrA' : b1 = Expr.mentionsConst TP et := hrA
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ :=
          ih m1 lv ev _ _ (b2, m2) hsA.ok
            ⟨denoteN_ext hT hsA.ext, denote_ext hval hsA.ext, hmA⟩ hc2
        have hrB' : b2 = Expr.mentionsConst TP ev := hrB
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨b3, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ :=
          ih m2 lb eb _ _ (b3, m3) hsB.ok
            ⟨denoteN_ext (denoteN_ext hT hsA.ext) hsB.ext,
             denote_ext (denote_ext hbd hsA.ext) hsB.ext, hmB⟩ hc3
        have hrC' : b3 = Expr.mentionsConst TP eb := hrC
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC)
          (by simp only [Expr.mentionsConst]; rw [hrA', hrB', hrC']) hmC hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ :=
          ih memo psub es _ _ (b1, m1) hok ⟨hT, hsub, hm⟩ hc1
        have hrA' : b1 = Expr.mentionsConst TP es := hrA
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin hsA
          (by simp only [Expr.mentionsConst]
              rw [hrA', beq_handle_eq hok.wf hn hT]) hmA hz

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:922-924 Expr.mentionsConstFast
The entry at an empty memo.

**CLOSED** (task #97-P3-Ind round 3): `mentionsConstGo_spec` at the empty
memo, which `MentionsMemoOK.empty` says is sound. -/
theorem mentionsConst_spec (T : NIdx) (TP : ConLeche.Name) (e : EIdx)
    (eP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP)
      (Arena.mentionsConst T e) (RV (Expr.mentionsConst TP eP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hT, hd⟩ := hp
  simp only [Arena.mentionsConst] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ :=
    mentionsConstGo_spec T TP ∅ Arena.coreWalkFuel e eP s₀ s₁ q hok
      ⟨hT, hd, MentionsMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

end ConRon.Bridge.Inductives

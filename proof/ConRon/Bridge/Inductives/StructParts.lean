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
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.ExprOps.Spine

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

`sorry`: `structFamI_spec` and one handle equality, which is `denoteE_inj`. -/
theorem structCtorResidOk_spec (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP o nIdx : Nat)
    (cbody : EIdx) (cbodyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cbody = some cbodyP)
      (Arena.structCtorResidOk T lps nP o nIdx cbody)
      (RV (ConLeche.structCtorResidOk TP lpsP nP o nIdx cbodyP)) := by
  sorry

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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
The shape facts the model reads off the stored (annotated) types.  A `Bool`
answer.

`sorry`: `stripPis`' spec (`Bridge/ExprOps/TelescopeF.lean`), the tag
dispatch through `Bridge/Rel.lean`'s `EStore.tagOf_of_view`, `structFam_spec`,
`structCtorSpine_spec` and five handle equalities through `denoteE_inj`. -/
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
  sorry

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

`sorry`: `structShape_spec`, `stripLams`' and `stripPis`' specs, the reserved
name table through `PinsOK`, `lvlEq?_spec` (closed) and `internNNode_spec` at
`T.str "rec"`. -/
theorem structPartsCore?_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (ROp RSParts (ConLeche.structPartsCore? blockP)) := by
  sorry

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

`sorry`: `structShape_spec`, `stripLams`' and `stripPis`' specs, and the
handle comparisons through `denoteN_inj`/`denoteE_inj`.  Exactly
`structPartsCore?_spec`'s dependencies MINUS `lvlEq?`: the two statements share
the dispatch and differ only in what they say about the record.  The intended
shape is one dispatch lemma feeding both; this round states the consumer's
half so the Frontend tier can cite it by name. -/
theorem structPartsCore?_isSome (block : List IConstantInfo)
    (blockP : List ConstantInfo) :
    PSpecP (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (fun _ r => r.isSome = (ConLeche.structPartsCore? blockP).isSome) := by
  sorry

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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:347-354 structProjResidP
The constructor type's residual after `i` projections have been substituted.

`sorry`: `Bridge/ExprOps/Owed.lean`'s `instPisAtLift_spec` — still open on
that tier's own list — plus `structProjPs_spec` and `structProjArgP_spec`. -/
theorem structProjResidP_spec (T : NIdx) (TP : ConLeche.Name) (nP : Nat)
    (cty : EIdx) (ctyP : Expr) (i : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjResidP T nP cty i)
      (ROp RE (ConLeche.structProjResidP TP nP ctyP i)) := by
  sorry

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

/-! ### `stripPis`, in run form

`Bridge/ExprOps/Spine.lean`'s `stripPis_spec` is CLOSED and this tier's three
telescope readers (`structUsedLater`, `structUsedLaterGo` and, through them,
`structProjGuards`) are its only consumers here.  Two inversions of
`denoteBP` are all the shape they need: this tier never looks at the peeled
binders, only at the residual. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the run form
at this tier's frame; `stripPis` is read-only, so the state does not move at
all. -/
theorem stripPis_pstep {k : Nat} {s₀ s' : AState} {c : EIdx} {cP : Expr}
    {r : Option (List (EIdx × BinderMeta) × EIdx)} (hok : StateOK s₀)
    (hd : denoteE s₀.store c = some cP)
    (hrun : Arena.stripPis k c s₀ = .ok (r, s')) :
    s' = s₀ ∧ ExprOps.denoteBP s₀.store r = some (Expr.stripPis k cP) := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.stripPis_spec k s₀ c hok (by rw [hd]; rfl))
  exact ⟨h1, h2 cP hd⟩

/-- con-leche: none — a `none` answer is `none` on the pure side too: the
two-sidedness `stripPis`' dispatch needs. -/
theorem stripPis_none {st : EStore} {k : Nat} {cP : Expr}
    (h : ExprOps.denoteBP st none = some (Expr.stripPis k cP)) :
    Expr.stripPis k cP = none := (Option.some.inj h).symm

/-- con-leche: none — and a `some` answer names the pure residual. -/
theorem stripPis_some {st : EStore} {k : Nat} {cP : Expr}
    {bs : List (EIdx × BinderMeta)} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some (Expr.stripPis k cP)) :
    ∃ xs x, Expr.stripPis k cP = some (xs, x) ∧ denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      exact ⟨xs, x, (Option.some.inj h).symm, rfl⟩

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

`sorry`: a `Nat` recursion over `instantiate1LiftFast_spec`
(`Bridge/ExprOps/Subst.lean`) and `structProjArgP_spec`. -/
theorem structProjBodiesGo_spec (T : NIdx) (TP : ConLeche.Name) (k i : Nat)
    (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP)
      (Arena.structProjBodiesGo T k i h)
      (ROp REL (ConLeche.structProjBodiesGo TP k i hP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:768-771 structProjBodies
The entry, after `nP` parameter binders.

`sorry`: `structProjBodiesGo_spec` and `structProjResidP_spec`. -/
theorem structProjBodies_spec (T : NIdx) (TP : ConLeche.Name) (nP nF : Nat)
    (cty : EIdx) (ctyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjBodies T nP nF cty)
      (ROp REA (ConLeche.structProjBodies TP nP nF ctyP)) := by
  sorry

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

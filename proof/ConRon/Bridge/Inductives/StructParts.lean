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
former's result sort and asks `lvlEq? s z` for `isProp`, and `lvlEq?` fills
two per-declaration cache tables — so `PStep`'s `caches` clause, which round 1
stated here, is false of it.  `structShape` itself is untouched and stays
pure: the `lvlEq?` call is in `structPartsCore?`'s own body.

`sorry`: `structShape_spec`, `stripLams`' and `stripPis`' specs, the reserved
name table through `PinsOK`, `lvlEq?_spec` (closed) and `internNNode_spec` at
`T.str "rec"`. -/
theorem structPartsCore?_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (ROp RSParts (ConLeche.structPartsCore? blockP)) := by
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

/-! ## `hasLooseBVarB`, memoised

`hasLooseBVarBIns` has NO statement of its own: it is the memo-insert helper
(con-leche's `Expr.hasLooseBVarBIns`), a pure function on `Bool ×
Std.HashMap` with no handle in it, and its content is entirely inside
`hasLooseBVarBGo_spec`'s invariant step.  Census class (S). -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
The memoised walk: the answer is the real one AND the memo it hands back is
still sound.

`sorry`: a fuel induction with the memo threaded, in
`Bridge/ExprOps/Walks.lean`'s shape, plus the `bvarB` cutoff
(`Bridge/ExprOps/Ranges.lean`'s `bvarB_spec`, closed) for the early return. -/
theorem hasLooseBVarBGo_spec (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ LooseMemoOK memo st)
      (Arena.hasLooseBVarBGo memo i fuel h)
      (fun st r => r.1 = Expr.hasLooseBVarB i hP ∧ LooseMemoOK r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:624-626 Expr.hasLooseBVarBFast
The entry: an empty memo is sound, so the answer is the real one.

`sorry`: `hasLooseBVarBGo_spec` at the empty memo. -/
theorem hasLooseBVarBFast_spec (i : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.hasLooseBVarBFast i e) (RV (Expr.hasLooseBVarB i eP)) := by
  sorry

/-! ## The projection guards -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:633-641 structUsedLater
Is field `j` mentioned by a later field's domain?

`sorry`: `hasLooseBVarBFast_spec` under the constructor type's telescope. -/
theorem structUsedLater_spec (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structUsedLater cty nP j)
      (RV (ConLeche.structUsedLater ctyP nP j)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:669-674 structUsedLaterGo
The same with the memo threaded (task #236's one shared memo across `nF`
calls).

`sorry`: `hasLooseBVarBGo_spec` under the telescope. -/
theorem structUsedLaterGo_spec (memo : Std.HashMap (EIdx × Nat) Bool)
    (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterGo memo cty nP j)
      (fun st r => r.1 = ConLeche.structUsedLater ctyP nP j ∧
        LooseMemoOK r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:685-692 structUsedLaterList
The `n` answers from `base` up, one memo through all of them.

`sorry`: a `Nat` recursion over `structUsedLaterGo_spec`. -/
theorem structUsedLaterList_spec (cty : EIdx) (ctyP : Expr) (nP : Nat)
    (memo : Std.HashMap (EIdx × Nat) Bool) (n base : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterList cty nP memo n base)
      (RV ((List.range n).map fun k => ConLeche.structUsedLater ctyP nP (base + k))) := by
  sorry

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

`sorry`: `structUsedLaterList_spec` and `zeroLevel`'s pin read
(`Bridge/Specs.lean`, closed). -/
theorem structProjGuards_spec (cty : EIdx) (ctyP : Expr) (nP nF : Nat)
    (sorts : List LIdx) (sortsP : List Level) :
    PSpec (fun st => denoteE st cty = some ctyP ∧
        denoteLList st.ls sorts = some sortsP)
      (Arena.structProjGuards cty nP nF sorts)
      (RLL (ConLeche.structProjGuards ctyP nP nF sortsP)) := by
  sorry

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

`sorry`: a fuel induction with the memo threaded; the name equality is
`denoteN_inj` (`Bridge/Rel.lean`), which is what makes handle inequality
structural inequality. -/
theorem mentionsConstGo_spec (T : NIdx) (TP : ConLeche.Name)
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        MentionsMemoOK TP memo st)
      (Arena.mentionsConstGo T memo fuel h)
      (fun st r => r.1 = Expr.mentionsConst TP hP ∧
        MentionsMemoOK TP r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:922-924 Expr.mentionsConstFast
The entry at an empty memo.

`sorry`: `mentionsConstGo_spec`. -/
theorem mentionsConst_spec (T : NIdx) (TP : ConLeche.Name) (e : EIdx)
    (eP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP)
      (Arena.mentionsConst T e) (RV (Expr.mentionsConst TP eP)) := by
  sorry

end ConRon.Bridge.Inductives

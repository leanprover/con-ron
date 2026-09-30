/-
# `ConRon.Bridge.Inductives.StructParts` — Theorem 1 for the generators

`Arena/Inductives/StructParts.lean`'s twins against
`ConLeche/Kernel/Inductives/StructParts.lean`: the parameter spines, the
elimination level, the constructor-residual test, the projection bodies and
guards, and the two memoised `Expr` predicates.  (The families, the Π→λ
rewrites and the structure recogniser went with con-leche's fixpoint route,
task #105, and their lemmas with them.)

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
from the others.

con-leche's own are `LooseBVarMemoInv` (`StructParts.lean:171-172`) and
`MentionsMemoInv` (`StructParts.lean:551-552`); the arena's are the same
predicate at handle keys, through `denoteE`.
-/
import ConRon.Bridge.Inductives.Rel

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The three memo invariants -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:171-172 LooseBVarMemoInv
The `(handle, cursor)`-keyed memo of `hasLooseBVarB`: every recorded answer is
the real one at the key's own cursor. -/
def LooseMemoOK (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ r = Expr.hasLooseBVarB k.2 e

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:551-552 MentionsMemoInv
The handle-keyed memo of `mentionsConst T`. -/
def MentionsMemoOK (T : ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsConst T e

/-- con-leche: none — the empty memo is sound. -/
theorem LooseMemoOK.empty {st : EStore} : LooseMemoOK ∅ st := by
  intro k r h; simp at h

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:177-189
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:557-568
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

/-! ## The spines -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:52-53 structPsAt
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:57-58 structElimLevel
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:82-85 structCtorResidOk
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
  have hlen : ps.length = nP := by
    have := denoteEList_len hps
    simpa [ConLeche.structPsAt] using this.symm
  rw [hlen, ConLeche.structCtorResidOk,
    beq_ehandle_eq hs5.ok.wf (denote_ext hfn hs5.ext) (denote_ext hhd hs5.ext),
    beq_ehandleList_eq hs5.ok.wf
      (denoteEList_take (denoteEList_ext hs5.ext _ _ hargs) nP) hps,
    denoteEList_len (denoteEList_ext hs5.ext _ _ hargs)]

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:92-93 structProjPs
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:92-93 structProjPs
The projection types' parameter spine. -/
theorem structProjPs_spec (nP : Nat) :
    PSpec PT (Arena.structProjPs nP) (REL (ConLeche.structProjPs nP)) := by
  rw [← structProjPs_eq]
  exact structPsAt_spec 1 nP

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:100-101 structProjArgP
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

/-! ### The pure side's own equations

`Expr.hasLooseBVarB` is `if e.bvarB ≤ i then false else <the ten-way walk>`,
so every arm of the twin's dispatch needs the same two-step unfolding.  These
are con-leche's `hasLooseBVarB_eq` proof's first line, once per shape. -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:132-145 (the `if`)
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:198-233 Expr.hasLooseBVarBGo
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:380-381 Expr.hasLooseBVarBFast
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

/-! ## The projection guards -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:393-396 structUsedLater
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:425-429 structUsedLaterGo
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-447 structUsedLaterList
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:404-411
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:404-411 structProjGuards
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:479-487 structProjGuardsFast
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:516-521 structProjBodiesGo
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
    obtain ⟨v0, hv0⟩ := denoteE_view hh
    obtain ⟨v, s1, k1, hz1⟩ := bindOk (tagIf_view_run hv0
      (fun hne => by cases v0 <;> first | rfl | exact absurd rfl hne) hrun)
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:523-526 structProjBodies
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:570-604 Expr.mentionsConstGo
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:678-679 Expr.mentionsConstFast
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

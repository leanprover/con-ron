/-
# `ConRon.Bridge.Inductives.Modeled` — Theorem 1 for the modeled route

`Arena/Inductives/Modeled.lean`'s thirty-three twins against
`ConLeche/Kernel/Inductives/Modeled.lean`: the iota certificates, the member
checks, the projection functions, the capability theorems and `checkModeled`
itself — the route `checkIndDecl` takes when `nativeParts?` does not
recognise the block.

## The rename map is DATA here and a FUNCTION there

Task #97d-2's deviation 3 answers the question task #97b left open:
`renameConsts`' `f : NIdx → NIdx` is a precomputed association list of
interned pairs (`blockRenameTable`, `projBack`, `projFwd`) and `renameBy` is
its lookup, "because over handles building a name means INTERNING one and a
pure `NIdx → NIdx` cannot".  `RenameRel` below is what that costs the proof:
the table denotes con-leche's `Name → Name` pointwise, at every handle that
denotes, and each of the three table builders has a statement saying so.

## `eqBasisStored` and the pinned `Eq`

Three clauses of this file ask `env.find? eqName = some eqA`.  The twin
compares HANDLES (`ci == (← eqA)`), which is the same predicate because
`denoteE`/`denoteN` are injective — DESIGN §8.3's soundness obligation, cashed
here for the third time in the campaign (after the Core tier's stuck-tag
branch and `defeqPeel_chain`'s two equality short-circuits).
-/
import ConRon.Bridge.Inductives.NativeInstall
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Frontend.Shared

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The rename map -/

/-- con-leche: none — **the rename TABLE denotes a rename FUNCTION**: at every
handle that denotes a name, the table's lookup denotes that function's value.
Task #97d-2's deviation 3, as a relation. -/
def RenameRel (st : EStore) (tbl : List (NIdx × NIdx))
    (f : ConLeche.Name → ConLeche.Name) : Prop :=
  ∀ (n : NIdx) (nm : ConLeche.Name), denoteN st.ns n = some nm →
    denoteN st.ns (Arena.renameBy tbl n) = some (f nm)

/-- con-leche: none — a rename relation survives an append, because both sides
are `denoteN` facts. -/
theorem RenameRel.ext {st st' : EStore} {tbl : List (NIdx × NIdx)}
    {f : ConLeche.Name → ConLeche.Name} (h : RenameRel st tbl f)
    (hx : Ext st st') (hinj : ∀ n nm, denoteN st'.ns n = some nm →
      denoteN st.ns n = some nm) : RenameRel st' tbl f :=
  fun n nm hn => hx.lss.ls.ns _ _ (h n nm (hinj n nm hn))

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
The block's own rename table: each member name `N` to `N._model`.

**STATEMENT DEFECT, round 4** (the campaign's tenth, this tier's fifth).
Round 1 quantified the rename FUNCTION — `(f : ConLeche.Name → ConLeche.Name)`
as a free parameter — and claimed the table denotes it.  That is false at
every `f` but one: a name the table does not mention is its own image, so
`RenameRel st r f` at a fresh name says `nm = f nm`.  The instantiation is
`checkMemberVal`'s own (`Modeled.lean:382`),
`fun n => if blockNames.contains n then n.str "_model" else n`, and naming it
is what makes the statement say something.  Nothing cited the old form.

**PROVED** (round 4): the list induction, with `internNNode_run` at each
member and `beq_handle_eq` at `renameBy`'s lookup — the `false` branch is
`denoteN_inj`, which is what turns "these are different handles" into "these
are different names" and lets `List.contains` step. -/
theorem blockRenameTable_spec (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) :
    PSpec (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP)
      (Arena.blockRenameTable blockNames)
      (fun st r => RenameRel st r
        (fun n => if blockNamesP.contains n then n.str "_model" else n)) := by
  induction blockNames generalizing blockNamesP with
  | nil =>
    intro s₀ s' r hok hd hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.blockRenameTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    intro q qm hq
    simpa [Arena.renameBy] using hq
  | cons n ns ih =>
    intro s₀ s' r hok hd hrun
    simp only [Frontend.denoteNList] at hd
    cases hn : denoteN s₀.store.ns n with
    | none => rw [hn] at hd; simp at hd
    | some nm =>
      cases hns : Frontend.denoteNList s₀.store.ns ns with
      | none => rw [hn, hns] at hd; simp at hd
      | some nms =>
        rw [hn, hns] at hd
        obtain rfl := Option.some.inj hd
        simp only [Arena.blockRenameTable] at hrun
        obtain ⟨m, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨hstep1, hm⟩ := internNNode_run hok
          (by intro c hc
              simp only [NNodeView.children, List.mem_singleton] at hc
              subst hc
              exact nview_isSome_of_denote hn) h1
        simp only [denoteNView, denoteN_ext hn hstep1.ext,
          Option.map_some] at hm
        obtain ⟨t, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨hstep2, hrel⟩ :=
          ih nms s₁ s₂ t hstep1.ok
            (denoteNListE_ext hstep1.ext _ _ hns) h3
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨hstep1.trans hstep2, ?_⟩
        intro q qm hq
        have hn' : denoteN s'.store.ns n = some nm :=
          denoteN_ext (denoteN_ext hn hstep1.ext) hstep2.ext
        have hm' : denoteN s'.store.ns m = some (nm.str "_model") :=
          denoteN_ext hm hstep2.ext
        have hbq := beq_handle_eq hstep2.ok.wf hn' hq
        cases hb : (n == q) with
        | true =>
          have hnm : (nm == qm) = true := by rw [← hbq]; exact hb
          obtain rfl := eq_of_beq hnm
          have hfind : ((n, m) :: t).find? (fun p => p.1 == q) = some (n, m) := by
            simp [hb]
          simp only [Arena.renameBy, hfind]
          have hct : (nm :: nms).contains nm = true := by simp
          simp only [hct, if_true]
          exact hm'
        | false =>
          have hne : (nm == qm) = false := by rw [← hbq]; exact hb
          have hrec := hrel q qm hq
          simp only [Arena.renameBy] at hrec ⊢
          have hfind : ((n, m) :: t).find? (fun p => p.1 == q)
              = t.find? (fun p => p.1 == q) := by simp [hb]
          rw [hfind]
          have hne' : ¬ (qm = nm) := by
            intro hc; rw [hc] at hne; simp at hne
          have hct : (nm :: nms).contains qm = nms.contains qm := by
            simp [hne']
          rw [hct]
          exact hrec

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName — the run
form: `(TP.str "_model").str ("proj_" ++ toString i)`, two interns. -/
theorem projModelName_run {s s' : AState} {T : NIdx} {TP : ConLeche.Name}
    {i : Nat} {h : NIdx} (hok : StateOK s)
    (hT : denoteN s.store.ns T = some TP)
    (hrun : Arena.projModelName T i s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = some (ConLeche.projModelName TP i) := by
  simp only [Arena.projModelName] at hrun
  obtain ⟨m, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, hm⟩ := internStrN_run hok hT k1
  obtain ⟨p2, hr⟩ := internStrN_run p1.ok hm h2
  exact ⟨p1.trans p2, hr⟩

/-- con-leche: ConLeche/Kernel/Env.lean:629 projFnName — the run form:
`(TP.str "proj").num i`, two interns. -/
theorem projFnName_run {s s' : AState} {T : NIdx} {TP : ConLeche.Name}
    {i : Nat} {h : NIdx} (hok : StateOK s)
    (hT : denoteN s.store.ns T = some TP)
    (hrun : Arena.projFnName T i s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = some (ConLeche.projFnName TP i) := by
  simp only [Arena.projFnName] at hrun
  obtain ⟨m, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, hm⟩ := internStrN_run hok hT k1
  obtain ⟨p2, hr⟩ := internNumN_run p1.ok hm h2
  exact ⟨p1.trans p2, hr⟩

/-- con-leche: none — the rename table's lookup at the empty table. -/
theorem renameBy_nil (n : NIdx) : Arena.renameBy [] n = n := rfl

/-- con-leche: none — and at a cons: `renameBy` is a `List.find?` on the
key, so one entry is one `if`.  The two table builders below are read through
this. -/
theorem renameBy_cons (a b n : NIdx) (rest : List (NIdx × NIdx)) :
    Arena.renameBy ((a, b) :: rest) n =
      if a == n then b else Arena.renameBy rest n := by
  cases h : (a == n) <;> simp [Arena.renameBy, h]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack —
**the projection half of the rename, as the RECURSION the arena runs**.
con-leche writes it as a `List.find?` over `List.range nF`; the arena's
`projBack.go` builds the table one field at a time, from `j` upwards, so the
induction wants this shape and `projBackTail_eq` identifies the two. -/
def projBackTail (TP : ConLeche.Name) : Nat → Nat → ConLeche.Name → ConLeche.Name
  | 0, _, nm => nm
  | k + 1, j, nm =>
    if nm == ConLeche.projModelName TP j then ConLeche.projFnName TP j
    else projBackTail TP k (j + 1) nm

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd —
the same the other way. -/
def projFwdTail (TP : ConLeche.Name) : Nat → Nat → ConLeche.Name → ConLeche.Name
  | 0, _, nm => nm
  | k + 1, j, nm =>
    if nm == ConLeche.projFnName TP j then ConLeche.projModelName TP j
    else projFwdTail TP k (j + 1) nm

/-- con-leche: none — the recursion IS con-leche's `List.find?`, generalised
over the starting index so the induction goes through (`List.range n` is
`List.range' 0 n`). -/
theorem projBackTail_eq (TP : ConLeche.Name) :
    ∀ (k j : Nat) (nm : ConLeche.Name),
      projBackTail TP k j nm =
        (match (List.range' j k).find?
            (fun i => nm == ConLeche.projModelName TP i) with
         | some i => ConLeche.projFnName TP i
         | none => nm) := by
  intro k
  induction k with
  | zero => intro j nm; simp [projBackTail, List.range']
  | succ k ih =>
    intro j nm
    rw [show List.range' j (k + 1) = j :: List.range' (j + 1) k by simp [List.range']]
    simp only [projBackTail, List.find?_cons, ih (j + 1) nm]
    split
    · rename_i h; rw [h]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      rw [h]

/-- con-leche: none — the same for `projFwd`. -/
theorem projFwdTail_eq (TP : ConLeche.Name) :
    ∀ (k j : Nat) (nm : ConLeche.Name),
      projFwdTail TP k j nm =
        (match (List.range' j k).find?
            (fun i => nm == ConLeche.projFnName TP i) with
         | some i => ConLeche.projModelName TP i
         | none => nm) := by
  intro k
  induction k with
  | zero => intro j nm; simp [projFwdTail, List.range']
  | succ k ih =>
    intro j nm
    rw [show List.range' j (k + 1) = j :: List.range' (j + 1) k by simp [List.range']]
    simp only [projFwdTail, List.find?_cons, ih (j + 1) nm]
    split
    · rename_i h; rw [h]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      rw [h]

/-- con-leche: none — `projBack`'s inner loop: the table it builds renames
every handle that denotes by `projBackTail`. -/
theorem projBackGo_run (T : NIdx) (TP : ConLeche.Name) :
    ∀ (k j : Nat) {s s' : AState} {r : List (NIdx × NIdx)},
      StateOK s → denoteN s.store.ns T = some TP →
      Arena.projBack.go T k j s = .ok (r, s') →
      PStep s s' ∧ ∀ (n : NIdx) (nm : ConLeche.Name),
        denoteN s'.store.ns n = some nm →
        denoteN s'.store.ns (Arena.renameBy r n) =
          some (projBackTail TP k j nm) := by
  intro k
  induction k with
  | zero =>
    intro j s s' r hok hT hrun
    simp only [Arena.projBack.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, fun n nm hn => by
      simpa only [renameBy_nil, projBackTail] using hn⟩
  | succ k ih =>
    intro j s s' r hok hT hrun
    simp only [Arena.projBack.go] at hrun
    obtain ⟨a, s1, k1, h2⟩ := bindOk hrun
    obtain ⟨p1, ha⟩ := projModelName_run hok hT k1
    obtain ⟨b, s2, k2, h3⟩ := bindOk h2
    obtain ⟨p2, hb⟩ := projFnName_run p1.ok (denoteN_ext hT p1.ext) k2
    obtain ⟨x, s3, k3, h4⟩ := bindOk h3
    obtain ⟨p3, hx⟩ := ih (j + 1) p2.ok (denoteN_ext hT (p1.ext.trans p2.ext)) k3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p1.trans (p2.trans p3), ?_⟩
    intro n nm hn
    have ha' : denoteN s'.store.ns a = some (ConLeche.projModelName TP j) :=
      denoteN_ext (denoteN_ext ha p2.ext) p3.ext
    have hb' : denoteN s'.store.ns b = some (ConLeche.projFnName TP j) :=
      denoteN_ext hb p3.ext
    rw [renameBy_cons, beq_handle_eq' p3.ok.wf ha' hn]
    simp only [projBackTail]
    split
    · exact hb'
    · exact hx n nm hn

/-- con-leche: none — the same for `projFwd`'s inner loop. -/
theorem projFwdGo_run (T : NIdx) (TP : ConLeche.Name) :
    ∀ (k j : Nat) {s s' : AState} {r : List (NIdx × NIdx)},
      StateOK s → denoteN s.store.ns T = some TP →
      Arena.projFwd.go T k j s = .ok (r, s') →
      PStep s s' ∧ ∀ (n : NIdx) (nm : ConLeche.Name),
        denoteN s'.store.ns n = some nm →
        denoteN s'.store.ns (Arena.renameBy r n) =
          some (projFwdTail TP k j nm) := by
  intro k
  induction k with
  | zero =>
    intro j s s' r hok hT hrun
    simp only [Arena.projFwd.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, fun n nm hn => by
      simpa only [renameBy_nil, projFwdTail] using hn⟩
  | succ k ih =>
    intro j s s' r hok hT hrun
    simp only [Arena.projFwd.go] at hrun
    obtain ⟨a, s1, k1, h2⟩ := bindOk hrun
    obtain ⟨p1, ha⟩ := projFnName_run hok hT k1
    obtain ⟨b, s2, k2, h3⟩ := bindOk h2
    obtain ⟨p2, hb⟩ := projModelName_run p1.ok (denoteN_ext hT p1.ext) k2
    obtain ⟨x, s3, k3, h4⟩ := bindOk h3
    obtain ⟨p3, hx⟩ := ih (j + 1) p2.ok (denoteN_ext hT (p1.ext.trans p2.ext)) k3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p1.trans (p2.trans p3), ?_⟩
    intro n nm hn
    have ha' : denoteN s'.store.ns a = some (ConLeche.projFnName TP j) :=
      denoteN_ext (denoteN_ext ha p2.ext) p3.ext
    have hb' : denoteN s'.store.ns b = some (ConLeche.projModelName TP j) :=
      denoteN_ext hb p3.ext
    rw [renameBy_cons, beq_handle_eq' p3.ok.wf ha' hn]
    simp only [projFwdTail]
    split
    · exact hb'
    · exact hx n nm hn

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
The projection-function names mapped BACK to the model's field projections.

**CLOSED** (task #97-P3-Ind round 5): `projModelName_run`/`projFnName_run` at
each field, `renameBy_cons` for the two head entries, and `beq_handle_eq'` —
the flipped handle comparison — at every lookup.  `projBackTail_eq` is what
turns the loop's own recursion into con-leche's `List.find?` over
`List.range nF`. -/
theorem projBack_spec (T ctor : NIdx) (TP ctorP : ConLeche.Name) (nF : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns ctor = some ctorP)
      (Arena.projBack T ctor nF)
      (fun st r => RenameRel st r (ConLeche.projBack TP ctorP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hct⟩ := hpre
  simp only [Arena.projBack] at hrun
  obtain ⟨tm, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok hT k1
  obtain ⟨cm, s2, k2, h3⟩ := bindOk h2
  obtain ⟨p2, hcm⟩ := internStrN_run p1.ok (denoteN_ext hct p1.ext) k2
  obtain ⟨x, s3, k3, h4⟩ := bindOk h3
  obtain ⟨p3, hx⟩ := projBackGo_run T TP nF 0 p2.ok
    (denoteN_ext hT (p1.ext.trans p2.ext)) k3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨p1.trans (p2.trans p3), ?_⟩
  intro n nm hn
  have htm' : denoteN s'.store.ns tm = some (TP.str "_model") :=
    denoteN_ext (denoteN_ext htm p2.ext) p3.ext
  have hcm' : denoteN s'.store.ns cm = some (ctorP.str "_model") :=
    denoteN_ext hcm p3.ext
  have hT' : denoteN s'.store.ns T = some TP :=
    denoteN_ext hT (p1.ext.trans (p2.ext.trans p3.ext))
  have hct' : denoteN s'.store.ns ctor = some ctorP :=
    denoteN_ext hct (p1.ext.trans (p2.ext.trans p3.ext))
  show denoteN s'.store.ns (Arena.renameBy _ n) =
    some (ConLeche.projBack TP ctorP nF nm)
  rw [renameBy_cons, renameBy_cons,
    beq_handle_eq' p3.ok.wf htm' hn, beq_handle_eq' p3.ok.wf hcm' hn]
  simp only [ConLeche.projBack]
  by_cases hc1 : nm = TP.str "_model"
  · subst hc1
    simp only [beq_self_eq_true, if_pos]
    exact hT'
  · rw [if_neg hc1, beq_eq_false_iff_ne.mpr hc1, if_neg (by simp)]
    by_cases hc2 : nm = ctorP.str "_model"
    · subst hc2
      simp only [beq_self_eq_true, if_pos]
      exact hct'
    · rw [if_neg hc2, beq_eq_false_iff_ne.mpr hc2, if_neg (by simp)]
      rw [hx n nm hn, projBackTail_eq TP nF 0 nm, List.range_eq_range']
      rfl

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
The same map the other way.

**CLOSED** (task #97-P3-Ind round 5): `projBack_spec`'s argument, with the
two head entries keyed on `T`/`ctor` rather than on their `_model`
companions. -/
theorem projFwd_spec (T ctor : NIdx) (TP ctorP : ConLeche.Name) (nF : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns ctor = some ctorP)
      (Arena.projFwd T ctor nF)
      (fun st r => RenameRel st r (ConLeche.projFwd TP ctorP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hct⟩ := hpre
  simp only [Arena.projFwd] at hrun
  obtain ⟨tm, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok hT k1
  obtain ⟨cm, s2, k2, h3⟩ := bindOk h2
  obtain ⟨p2, hcm⟩ := internStrN_run p1.ok (denoteN_ext hct p1.ext) k2
  obtain ⟨x, s3, k3, h4⟩ := bindOk h3
  obtain ⟨p3, hx⟩ := projFwdGo_run T TP nF 0 p2.ok
    (denoteN_ext hT (p1.ext.trans p2.ext)) k3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨p1.trans (p2.trans p3), ?_⟩
  intro n nm hn
  have htm' : denoteN s'.store.ns tm = some (TP.str "_model") :=
    denoteN_ext (denoteN_ext htm p2.ext) p3.ext
  have hcm' : denoteN s'.store.ns cm = some (ctorP.str "_model") :=
    denoteN_ext hcm p3.ext
  have hT' : denoteN s'.store.ns T = some TP :=
    denoteN_ext hT (p1.ext.trans (p2.ext.trans p3.ext))
  have hct' : denoteN s'.store.ns ctor = some ctorP :=
    denoteN_ext hct (p1.ext.trans (p2.ext.trans p3.ext))
  show denoteN s'.store.ns (Arena.renameBy _ n) =
    some (ConLeche.projFwd TP ctorP nF nm)
  rw [renameBy_cons, renameBy_cons,
    beq_handle_eq' p3.ok.wf hT' hn, beq_handle_eq' p3.ok.wf hct' hn]
  simp only [ConLeche.projFwd]
  by_cases hc1 : nm = TP
  · subst hc1
    simp only [beq_self_eq_true, if_pos]
    exact htm'
  · rw [if_neg hc1, beq_eq_false_iff_ne.mpr hc1, if_neg (by simp)]
    by_cases hc2 : nm = ctorP
    · subst hc2
      simp only [beq_self_eq_true, if_pos]
      exact hcm'
    · rw [if_neg hc2, beq_eq_false_iff_ne.mpr hc2, if_neg (by simp)]
      rw [hx n nm hn, projFwdTail_eq TP nF 0 nm, List.range_eq_range']
      rfl

/-! ## Two helpers the modeled route owns -/

open Std.Do in
set_option mvcgen.warning false in
/-- con-leche: ConLeche/Kernel/ExprOps.lean:1112-1114 renameConstsFast —
`Bridge/ExprOps/Owed.lean`'s `renameConstsFast_spec` with the NAME store's
frame kept: the walk interns expression nodes only, which `RenameSpec` states
(`s'.store.ns = ns0`) and the entry point dropped.  `RenameRel` mentions only
the name store, so this is what carries a rename relation across a rename. -/
theorem renameConstsFast_ns (fuel : Nat) (f : NIdx → NIdx)
    (g : ConLeche.Name → ConLeche.Name) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN s₀.store.ns n = some x →
      denoteN s₀.store.ns (f n) = some (g x))
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameConstsFast fuel f e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.store.ns = s₀.store.ns ∧
        RelE (Expr.renameConsts g) s₀.store e s'.store r⌝⦄ := by
  have hr := (ExprOps.renameConstsGo_specS f g s₀.store.ns hf fuel).run
  mvcgen [renameConstsFast, hr]
  all_goals bridge_vcs [Expr.renameConsts, BMExt]

/-- con-leche: none — the run form, at this tier's frame. -/
theorem renameConstsFast_pstep {fuel : Nat} {tbl : List (NIdx × NIdx)}
    {fP : ConLeche.Name → ConLeche.Name} {s₀ s' : AState} {e r : EIdx} {eP : Expr}
    (hok : StateOK s₀) (hren : RenameRel s₀.store tbl fP)
    (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.renameConstsFast fuel (Arena.renameBy tbl) e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ s'.store.ns = s₀.store.ns ∧
      denoteE s'.store r = some (eP.renameConsts fP) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (renameConstsFast_ns fuel _ fP s₀ e hok hren (by rw [hd]; rfl))
  exact ⟨PStep.of_caches h1 h2 h3 h4 h5, h6, h7 eP hd⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux — the
range peeled at its TOP, which is the order the twin's recursion runs in. -/
theorem domsMatchAux_succ (g : Nat → Expr → Expr) (bs₁ bs₂ : List (Expr × BinderMeta))
    (o₁ o₂ k : Nat) :
    ConLeche.domsMatchAux g bs₁ bs₂ o₁ o₂ (k + 1) =
      (ConLeche.domsMatchAux g bs₁ bs₂ o₁ o₂ k &&
        (match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
         | some b₁, some b₂ => b₁.1 == g k b₂.1
         | _, _ => false)) := by
  simp only [ConLeche.domsMatchAux, List.range_succ, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true]
  rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux —
`domsMatchAux` with the right side renamed; con-leche's higher-order `g` is
instantiated at `fun _ e => e.renameConsts fP`, which is `checkProjIota`'s own
instance of it.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem domsMatchRenamed_spec (tbl : List (NIdx × NIdx))
    (fP : ConLeche.Name → ConLeche.Name) (bs₁ bs₂ : List (EIdx × BinderMeta))
    (bs₁P bs₂P : List (Expr × BinderMeta)) (o₁ o₂ k : Nat) :
    PSpec (fun st => RenameRel st tbl fP ∧
        denoteBinders st bs₁ = some bs₁P ∧ denoteBinders st bs₂ = some bs₂P)
      (Arena.domsMatchRenamed (Arena.renameBy tbl) bs₁ bs₂ o₁ o₂ k)
      (RV (ConLeche.domsMatchAux (fun _ e => e.renameConsts fP) bs₁P bs₂P
        o₁ o₂ k)) := by
  induction k with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.domsMatchRenamed] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | succ k ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hren, h1, h2⟩ := hpre
    show PStep s₀ s' ∧ r = _
    rw [domsMatchAux_succ]
    simp only [Arena.domsMatchRenamed] at hrun
    obtain ⟨hA1, hB1⟩ := denoteBinders_getElem? h1 (o₁ + k)
    obtain ⟨hA2, hB2⟩ := denoteBinders_getElem? h2 (o₂ + k)
    cases hb1 : bs₁[o₁ + k]? with
    | none =>
      rw [hb1] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, by simp only [hB1 hb1, Bool.and_false]⟩
    | some p1 =>
    obtain ⟨t1, m1⟩ := p1
    obtain ⟨t1P, hp1, hd1⟩ := hA1 t1 m1 hb1
    cases hb2 : bs₂[o₂ + k]? with
    | none =>
      rw [hb1, hb2] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, by simp only [hp1, hB2 hb2, Bool.and_false]⟩
    | some p2 =>
    obtain ⟨t2, m2⟩ := p2
    obtain ⟨t2P, hp2, hd2⟩ := hA2 t2 m2 hb2
    rw [hb1, hb2] at hrun
    dsimp only at hrun
    obtain ⟨rr, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1', hns, hrr⟩ := renameConstsFast_pstep hok hren hd2 k1
    have e1 := beq_ehandle_eq p1'.ok.wf (denote_ext hd1 p1'.ext) hrr
    rw [e1] at z1
    split at z1
    case isTrue hc =>
      have hren1 : RenameRel s1.store tbl fP := by
        intro n nm hn; rw [hns] at hn ⊢; exact hren n nm hn
      obtain ⟨p2', hr⟩ := ih s1 s' r p1'.ok
        ⟨hren1, denoteBinders_ext p1'.ext _ _ h1, denoteBinders_ext p1'.ext _ _ h2⟩ z1
      refine ⟨p1'.trans p2', ?_⟩
      rw [hr]
      simp only [hp1, hp2]
      rw [hc, Bool.and_true]
    case isFalse hc =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1', ?_⟩
      simp only [hp1, hp2]
      simp only [Bool.not_eq_true] at hc
      rw [hc, Bool.and_false]

/-- con-leche: none — `Frontend.denoteCV` is injective (a local copy of
`Bridge/Checker/Basis.lean`'s, which this tier does not import). -/
theorem denoteCV_inj' {st : EStore} (hwf : StoreWF st) {v w : IConstantVal}
    {c : ConstantVal} (hv : Frontend.denoteCV st v = some c)
    (hw : Frontend.denoteCV st w = some c) : v = w := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨h1, h2, h3⟩ := denoteCV_inv hv
  obtain ⟨g1, g2, g3⟩ := denoteCV_inv hw
  cases v; cases w
  simp only at h1 h2 h3 g1 g2 g3
  rw [denoteN_inj hrk.nsWF h1 g1, denoteNList_inj hwf _ _ _ h2 g2,
    denoteE_inj hwf h3 g3]

/-- con-leche: none — `Frontend.denoteCI` is injective at an inductive (it is
NOT injective at a projection table, whose `tableName` it drops).  A local
copy of `Bridge/Checker/Basis.lean`'s `denoteCI_inj_ind`. -/
theorem denoteCI_inj_ind' {st : EStore} (hwf : StoreWF st) {ci ci' : IConstantInfo}
    {cv : ConstantVal} {d : IndCaps}
    (h : Frontend.denoteCI st ci = some (.indInfo cv d))
    (h' : Frontend.denoteCI st ci' = some (.indInfo cv d)) : ci = ci' := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  have key : ∀ {x : IConstantInfo}, Frontend.denoteCI st x = some (.indInfo cv d) →
      ∃ v cap, x = .indInfo v cap ∧ Frontend.denoteCV st v = some cv ∧
        Frontend.denoteCaps st cap = some d := by
    intro x hx
    cases x with
    | indInfo v cap =>
      obtain ⟨cv', d', he, hv, hc⟩ := denoteCI_ind_inv hx
      cases he
      exact ⟨v, cap, rfl, hv, hc⟩
    | axiomInfo v => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv hx; cases he
    | ctorInfo v _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv hx; cases he
    | defnInfo v _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv hx; cases he
    | thmInfo v _ => obtain ⟨_, _, he, _⟩ := denoteCI_thm_inv hx; cases he
    | recInfo v _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv hx; cases he
    | projInfo t => obtain ⟨_, he, _⟩ := denoteCI_proj_inv hx; cases he
  obtain ⟨v, cap, rfl, hv, hc⟩ := key h
  obtain ⟨w, cap', rfl, hw, hc'⟩ := key h'
  obtain rfl := denoteCV_inj' hwf hv hw
  congr 1
  simp only [Frontend.denoteCaps] at hc hc'
  cases he : denoteN st.ns cap.etaCtor with
  | none => rw [he] at hc; simp at hc
  | some ct =>
    cases he' : denoteN st.ns cap'.etaCtor with
    | none => rw [he'] at hc'; simp at hc'
    | some ct' =>
      rw [he] at hc; rw [he'] at hc'
      rw [← hc'] at hc
      simp only [Option.some.injEq, IndCaps.mk.injEq] at hc
      obtain ⟨e1, rfl, e3, e4, e5, e6, e7, e8⟩ := hc
      have := denoteN_inj hrk.nsWF he he'
      cases cap; cases cap'
      simp_all

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
The "requires the pinned `Eq` basis" guard: `env.find? eqName = some eqA`.

**CLOSED** (task #97-P3-Ind round 7): `pinAt_run` for the name,
`IFEnvOK`'s `hit`/`miss` pair for the lookup, `Bridge/Frontend/Shared.lean`'s
scratch-agnostic `internCI_sstep` for the interned `eqA` (round 6's wall 3,
removed by task #97-P3-Frontend round 6), and `denoteCI_inj_ind'` for the
handle comparison — `eqA` is an inductive, where the denotation IS injective.
The frame is `IStepS`'s, read as a `CoreStep`. -/
theorem eqBasisStored_spec {μ : CheckMode} {env : Env} (fe : IFEnv) :
    CSpec μ env fe (fun st => denoteFEnv st fe = some env)
      (Arena.eqBasisStored fe)
      (RV (decide (env.find? ConLeche.eqName = some ConLeche.eqA))) := by
  intro s₀ s' r hok _ hrun
  simp only [Arena.eqBasisStored] at hrun
  obtain ⟨n, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hn⟩ := pinAt_run (x := ConLeche.eqName) hok.pins rfl k1
  rw [hs1] at z1
  cases hf : fe.find? n with
  | none =>
    rw [hf] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨CoreStep.refl hok, ?_⟩
    show false = _
    simp [IFEnvOK.miss hok.state hok.ienv hn hf]
  | some ci =>
  rw [hf] at z1
  obtain ⟨nm, cP, hnm, hci, henv⟩ := hok.ienv.hit n ci hf
  obtain rfl : nm = ConLeche.eqName := Option.some.inj (hnm.symm.trans hn)
  dsimp only at z1
  obtain ⟨c, s2, k2, z2⟩ := bindOk z1
  simp only [Arena.eqA, Arena.internCI] at k2
  obtain ⟨mc, s3, k3, z3⟩ := bindOk k2
  obtain ⟨rfl, rfl⟩ := pureOk z3
  obtain ⟨hstep, hc, -, -⟩ := Frontend.internCI_sstep hok.state (Frontend.EMemoOK.empty _) k3
  obtain ⟨rfl, rfl⟩ := pureOk z2
  refine ⟨⟨hok.monoF hstep.ok hstep.ext (CacheFrame.of_eq hstep.caches hstep.ext)
    hstep.pins, hstep.ext, hstep.pins⟩, ?_⟩
  show (ci == mc.2) = _
  rw [henv]
  have hci' := denoteCI_ext hci hstep.ext
  obtain ⟨cvE, dE, hE⟩ : ∃ cv d, ConLeche.eqA = .indInfo cv d := ⟨_, _, rfl⟩
  rw [hE] at hc ⊢
  by_cases heq : ci = mc.2
  · subst heq
    rw [hci'] at hc
    simp [Option.some.inj hc]
  · have : cP ≠ .indInfo cvE dE := by
      rintro rfl
      exact heq (denoteCI_inj_ind' hstep.ok.wf hci' hc)
    simp [heq, this]

/-! ## The iota certificates -/

/-- con-leche: none — `.app (.app (.app (.const c [ℓ]) ty) l) r` spelled once
over handles; three checks of this module match it.

**PROVED** (round 4): four `view_run` dispatches and a `viewLs_run`, with
`Bridge/Rel.lean`'s `denote_app_inv` / `denote_const_inv` at each step.  The
twin is read-only, so every arm's frame is `PStep.refl`; the nine non-matching
arms of each dispatch answer `none` and the statement is an implication out of
`some`, so they close on the `Option` constructor alone. -/
theorem eqApp3?_spec (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP)
      (Arena.eqApp3? h)
      (fun st r => ∀ c u ty l rr, r = some (c, u, ty, l, rr) →
        ∃ cP uP tyP lP rrP, denoteN st.ns c = some cP ∧
          denoteL st.ls u = some uP ∧ denoteE st ty = some tyP ∧
          denoteE st l = some lP ∧ denoteE st rr = some rrP ∧
          hP = .app (.app (.app (.const cP [uP]) tyP) lP) rrP) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.eqApp3?] at hrun
  obtain ⟨v1, s1, g1, k1⟩ := bindOk hrun
  obtain ⟨rfl, hw1⟩ := view_run g1
  cases v1
  case app f1 rr =>
    obtain ⟨efP, errP, rfl, hf1, hrr⟩ := denote_app_inv hok.wf hw1 hd
    obtain ⟨v2, s2, g2, k2⟩ := bindOk k1
    obtain ⟨rfl, hw2⟩ := view_run g2
    cases v2
    case app f2 l =>
      obtain ⟨ef2P, elP, hfe, hf2, hl⟩ := denote_app_inv hok.wf hw2 hf1
      obtain ⟨v3, s3, g3, k3⟩ := bindOk k2
      obtain ⟨rfl, hw3⟩ := view_run g3
      cases v3
      case app f3 ty =>
        obtain ⟨ef3P, etyP, hfe2, hf3, hty⟩ := denote_app_inv hok.wf hw3 hf2
        obtain ⟨v4, s4, g4, k4⟩ := bindOk k3
        obtain ⟨rfl, hw4⟩ := view_run g4
        cases v4
        case const c us =>
          obtain ⟨cP, lsP, hfe3, hc, hus⟩ := denote_const_inv hok.wf hw4 hf3
          obtain ⟨vs, s5, g5, k5⟩ := bindOk k4
          obtain ⟨rfl, hw5⟩ := viewLs_run g5
          have hvs := denoteLs_of_view hw5 hus
          cases vs with
          | nil =>
            obtain ⟨rfl, rfl⟩ := pureOk k5
            exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩
          | cons lv tl =>
            cases tl with
            | nil =>
              obtain ⟨rfl, rfl⟩ := pureOk k5
              refine ⟨PStep.refl hok, ?_⟩
              intro a b cc d e hh
              simp only [Option.some.injEq, Prod.mk.injEq] at hh
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hh
              simp only [denoteLList, opt2] at hvs
              cases hlv : denoteL s'.store.ls lv with
              | none => rw [hlv] at hvs; simp at hvs
              | some uP =>
                rw [hlv] at hvs
                simp only [Option.some.injEq] at hvs
                subst hvs
                subst hfe3
                subst hfe2
                subst hfe
                refine ⟨cP, uP, etyP, elP, errP, hc, ?_, hty, hl, hrr, rfl⟩
                first | exact hlv | rfl
            | cons _ _ =>
              obtain ⟨rfl, rfl⟩ := pureOk k5
              exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩
        all_goals
          (obtain ⟨rfl, rfl⟩ := pureOk k4
           exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩)
      all_goals
        (obtain ⟨rfl, rfl⟩ := pureOk k3
         exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩)
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk k2
       exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩)
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk k1
     exact ⟨PStep.refl hok, by intro a b cc d e hh; simp at hh⟩)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:31-53 checkIotaSidesTy
The two sides of a model iota theorem have the certified type.

**CLOSED** (task #97-P3-Ind round 7): `CoreSpec.knot`'s `infer` and `defeq`
slots, three and three, one fuel by `max`.

**Two preconditions it was missing** (round 7, §R6.3's repair): `EnvWF env`
and the scope of its three subjects at `depth` — the slots' own; the inferred
types' scope is `SimE`'s. -/
theorem checkIotaSidesTy_spec {μ : CheckMode} {env : Env} (feSelf : IFEnv)
    (envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (depth : Nat)
    (alphaS lhsS rhsS : EIdx) (alphaSP lhsSP rhsSP : Expr) (lA : LIdx)
    (lAP : Level) (cvName : NIdx) (cvNameP : ConLeche.Name)
    (hws : Expr.WScoped depth alphaSP ∧ Expr.WScoped depth lhsSP ∧
      Expr.WScoped depth rhsSP) :
    CSpec μ env feSelf
      (fun st => denoteE st alphaS = some alphaSP ∧
        denoteE st lhsS = some lhsSP ∧ denoteE st rhsS = some rhsSP ∧
        denoteL st.ls lA = some lAP ∧ denoteN st.ns cvName = some cvNameP ∧
        denoteFEnv st feSelf = some envSelf ∧ denoteFEnv st feSelf = some env)
      (Arena.checkIotaSidesTy μ feSelf depth alphaS lhsS rhsS lA cvName)
      (fun _ _ => ∃ F, ConLeche.checkIotaSidesTy μ (ConLeche.fueledOps μ F)
        envSelf depth alphaSP lhsSP rhsSP lAP cvNameP = .ok ()) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hal, hl, hr, hlA, -, hfeS, hfe⟩ := hpre
  obtain rfl : envSelf = env := Option.some.inj (hfeS.symm.trans hfe)
  obtain ⟨hwa, hwl, hwr⟩ := hws
  have hknot := hk.knot envSelf feSelf henv
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkIotaSidesTy] at hrun
  -- the left side's type
  obtain ⟨tl, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨ok1, x1, p1, ⟨tlP, htl, hwtl, F1, hF1⟩⟩ := AM.of_run (P := fun u => u = s₀)
    (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s₀.store u.store ∧
      u.pins = s₀.pins ∧ Core.SimE (ConLeche.inferTypeCore μ envSelf) depth lhsSP u.store r)
    rfl k1 (hknot.infer s₀ depth lhsS lhsSP hok hl hwl)
  obtain ⟨b1, s2, k2, z2⟩ := bindOk z1
  obtain ⟨ok2, x2, p2, ⟨F2, hF2⟩⟩ := AM.of_run (P := fun u => u = s1)
    (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s1.store u.store ∧
      u.pins = s1.pins ∧ Core.SimV (ConLeche.isDefEqCore μ envSelf) depth tlP alphaSP r)
    rfl k2 (hknot.defeq s1 depth tl alphaS tlP alphaSP ok1 htl (denote_ext hal x1) hwtl hwa)
  obtain ⟨hb1, z3⟩ := AM.dunless_ok hnever z2
  replace z3 := AM.pure_bind_ok z3
  subst hb1
  -- the right side's type
  obtain ⟨tr, s3, k3, z4⟩ := bindOk z3
  have x12 := x1.trans x2
  obtain ⟨ok3, x3, p3, ⟨trP, htr, hwtr, F3, hF3⟩⟩ := AM.of_run (P := fun u => u = s2)
    (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s2.store u.store ∧
      u.pins = s2.pins ∧ Core.SimE (ConLeche.inferTypeCore μ envSelf) depth rhsSP u.store r)
    rfl k3 (hknot.infer s2 depth rhsS rhsSP ok2 (denote_ext hr x12) hwr)
  obtain ⟨b2, s4, k4, z5⟩ := bindOk z4
  obtain ⟨ok4, x4, p4, ⟨F4, hF4⟩⟩ := AM.of_run (P := fun u => u = s3)
    (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s3.store u.store ∧
      u.pins = s3.pins ∧ Core.SimV (ConLeche.isDefEqCore μ envSelf) depth trP alphaSP r)
    rfl k4 (hknot.defeq s3 depth tr alphaS trP alphaSP ok3 htr
      (denote_ext hal (x12.trans x3)) hwtr hwa)
  obtain ⟨hb2, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  subst hb2
  have x14 := (x12.trans x3).trans x4
  have c4 : CoreStep μ envSelf feSelf s₀ s4 :=
    ⟨ok4, x14, by rw [p4, p3, p2, p1]⟩
  have e1 : ∀ F, F1 ≤ F → ConLeche.inferTypeCore μ envSelf F depth lhsSP = .ok tlP :=
    fun F h => ConLeche.inferTypeCore_mono h hF1
  have e2 : ∀ F, F2 ≤ F → ConLeche.isDefEqCore μ envSelf F depth tlP alphaSP = .ok true :=
    fun F h => ConLeche.isDefEqCore_mono h hF2
  have e3 : ∀ F, F3 ≤ F → ConLeche.inferTypeCore μ envSelf F depth rhsSP = .ok trP :=
    fun F h => ConLeche.inferTypeCore_mono h hF3
  have e4 : ∀ F, F4 ≤ F → ConLeche.isDefEqCore μ envSelf F depth trP alphaSP = .ok true :=
    fun F h => ConLeche.isDefEqCore_mono h hF4
  cases htt : μ.ttChecks with
  | false =>
    rw [htt] at z6
    simp only [Bool.false_eq_true, if_false] at z6
    obtain ⟨rfl, rfl⟩ := pureOk z6
    refine ⟨c4, max (max F1 F2) (max F3 F4), ?_⟩
    generalize hFm : max (max F1 F2) (max F3 F4) = Fm
    simp only [ConLeche.checkIotaSidesTy, ConLeche.fueledOps, bind, Except.bind,
      e1 Fm (by omega), e2 Fm (by omega), e3 Fm (by omega), e4 Fm (by omega), htt]
    rfl
  | true =>
    rw [htt] at z6
    simp only [if_true] at z6
    obtain ⟨ta, s5, k5, z7⟩ := bindOk z6
    obtain ⟨ok5, x5, p5, ⟨taP, hta, hwta, F5, hF5⟩⟩ := AM.of_run (P := fun u => u = s4)
      (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s4.store u.store ∧
        u.pins = s4.pins ∧ Core.SimE (ConLeche.inferTypeCore μ envSelf) depth alphaSP u.store r)
      rfl k5 (hknot.infer s4 depth alphaS alphaSP ok4 (denote_ext hal x14) hwa)
    obtain ⟨so, s6, k6, z8⟩ := bindOk z7
    obtain ⟨p6, hso⟩ := internSortE_run ok5.state (denoteL_ext hlA (x14.trans x5)) k6
    have ok6 := (p6.toCore ok5).ok
    obtain ⟨b3, s7, k7, z9⟩ := bindOk z8
    obtain ⟨ok7, x7, p7, ⟨F6, hF6⟩⟩ := AM.of_run (P := fun u => u = s6)
      (Q := fun r u => CheckOK μ envSelf feSelf u ∧ Ext s6.store u.store ∧
        u.pins = s6.pins ∧ Core.SimV (ConLeche.isDefEqCore μ envSelf) depth taP (.sort lAP) r)
      rfl k7 (hknot.defeq s6 depth ta so taP (.sort lAP) ok6 (denote_ext hta p6.ext) hso hwta
        (by simp [Expr.WScoped]))
    obtain ⟨hb3, z10⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail _) z9
    subst hb3
    obtain ⟨rfl, rfl⟩ := pureOk z10
    refine ⟨⟨ok7, (x14.trans x5).trans (p6.ext.trans x7), by rw [p7, p6.pins, p5, c4.pins]⟩,
      max (max (max F1 F2) (max F3 F4)) (max F5 F6), ?_⟩
    have e5 : ∀ F, F5 ≤ F → ConLeche.inferTypeCore μ envSelf F depth alphaSP = .ok taP :=
      fun F h => ConLeche.inferTypeCore_mono h hF5
    have e6 : ∀ F, F6 ≤ F →
        ConLeche.isDefEqCore μ envSelf F depth taP (.sort lAP) = .ok true :=
      fun F h => ConLeche.isDefEqCore_mono h hF6
    generalize hFm : max (max (max F1 F2) (max F3 F4)) (max F5 F6) = Fm
    simp only [ConLeche.checkIotaSidesTy, ConLeche.fueledOps, bind, Except.bind,
      e1 Fm (by omega), e2 Fm (by omega), e3 Fm (by omega), e4 Fm (by omega), htt,
      e5 Fm (by omega), e6 Fm (by omega)]
    rfl

/-- con-leche: none — the name of a recursor's `j`-th model iota theorem.

**STATEMENT DEFECT, round 4** (the campaign's ninth, this tier's fourth).
Round 1 stated the answer as `(cvNameP.str "iota").num j`, which is not the
name either side builds: con-leche's three call sites
(`ConLeche/Kernel/Inductives/Modeled.lean:73`, `:170`, `:216`) all spell
`(cvName.str "_model").str s!"iota_{j}"` and the twin interns exactly that.
The old statement was therefore FALSE — a transcription slip, not a gap — and
nothing had cited it yet, so the correction costs its three consumers nothing.

**PROVED** (round 4): `internNNode_run` twice, with `denoteN_ext` carrying the
first handle's denotation across the second intern. -/
theorem iotaThmName_spec (cvName : NIdx) (cvNameP : ConLeche.Name) (j : Nat) :
    PSpec (fun st => denoteN st.ns cvName = some cvNameP)
      (Arena.iotaThmName cvName j)
      (RN ((cvNameP.str "_model").str ("iota_" ++ toString j))) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.iotaThmName] at hrun
  obtain ⟨m, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hm⟩ := internNNode_run hok
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hd) h1
  simp only [denoteNView, denoteN_ext hd hstep1.ext, Option.map_some] at hm
  obtain ⟨hstep2, hr⟩ := internNNode_run hstep1.ok
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hm) h2
  refine ⟨hstep1.trans hstep2, ?_⟩
  simp only [denoteNView, denoteN_ext hm hstep2.ext, Option.map_some] at hr
  exact hr

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
**The plain iota certificate**: the `j`-th rule's model theorem is the stated
equation, its sides the rule's own.

`sorry`: `iotaThmName_spec`, `eqApp3?_spec`, `checkIotaSidesTy_spec`,
`Bridge/ExprOps/Reset.lean`'s `renameConstsFast_spec`, `CoreSpec.knot`'s
`defeq` slot, and `IFEnvOK` at the theorem's lookup. -/
theorem checkIotaThm_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) (cvj : IConstantVal) (cvjP : ConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (rhsAP : Expr) :
    CSpec μ env fe'
      (fun st => RenameRel st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        Frontend.denoteCV st cvj = some cvjP ∧ denoteE st rhsA = some rhsAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st fe' = some env)
      (Arena.checkIotaThm μ fe' feSelf tbl cvName lps tyA mI rP j r cvj cnP
        cnF rhsA)
      (fun _ _ => ∃ F, ConLeche.checkIotaThm μ (ConLeche.fueledOps μ F) env'
        envSelf fP cvNameP lpsP tyAP mI rP j rP' cvjP cnP cnF rhsAP
        = .ok ()) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
The nested rule's levels and pinned arguments, read off the stored recursor
type.  PURE on both sides (con-leche's is not even in `m`), and the answer is
a level list and an expression list — task #97d-2's deviation 6 keeps the
levels a `List LIdx`.

`sorry`: `stripPis`' spec and `Bridge/ExprOps/Spine.lean`'s `getAppSpine`. -/
theorem nestedRuleShape_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (cvName : NIdx) (cvNameP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr)
    (mI rP cnP j : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf)
      (Arena.nestedRuleShape fe' feSelf cvName lps tyA mI rP cnP j)
      (ROp (fun q st r => denoteLList st.ls r.1 = some q.1 ∧
          Frontend.denoteEList st r.2 = some q.2)
        (ConLeche.nestedRuleShape env' envSelf cvNameP lpsP tyAP mI rP cnP j)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
**The nested iota certificate**, which also decides the rule's firing mode.

`sorry`: `nestedRuleShape_spec`, `checkIotaThm_spec`'s pieces, and
`Frontend.denoteFire` at the answer. -/
theorem checkIotaThmN_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) (cvj : IConstantVal) (cvjP : ConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (rhsAP : Expr) :
    CSpec μ env fe'
      (fun st => RenameRel st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        Frontend.denoteCV st cvj = some cvjP ∧ denoteE st rhsA = some rhsAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st fe' = some env)
      (Arena.checkIotaThmN μ fe' feSelf tbl cvName lps tyA mI rP j r cvj cnP
        cnF rhsA)
      (fun st x => ∃ F fire, ConLeche.checkIotaThmN μ (ConLeche.fueledOps μ F)
        env' envSelf fP cvNameP lpsP tyAP mI rP j rP' cvjP cnP cnF rhsAP
          = .ok fire ∧ Frontend.denoteFire st x = some fire) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
One rule certified and its firing mode written in.

`sorry`: `checkIotaThm_spec`, `checkIotaThmN_spec` and `IFEnvOK` at the
constructor's lookup. -/
theorem checkIotaRule_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) :
    CSpec μ env fe'
      (fun st => RenameRel st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st fe' = some env)
      (Arena.checkIotaRule μ fe' feSelf tbl cvName lps tyA mI rP j r)
      (fun st x => ∃ F rl, ConLeche.checkIotaRule μ (ConLeche.fueledOps μ F)
        env' envSelf fP cvNameP lpsP tyAP mI rP j rP' = .ok rl ∧
        Frontend.denoteRule st x = some rl) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:362-371 checkIotaRules
The whole rule list.

`sorry`: a list induction over `checkIotaRule_spec`. -/
theorem checkIotaRules_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (rs : List IRecRule) (rsP : List RecRule) :
    CSpec μ env fe'
      (fun st => RenameRel st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRules st rs = some rsP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st fe' = some env)
      (Arena.checkIotaRules μ fe' feSelf tbl cvName lps tyA mI rP j rs)
      (fun st x => ∃ F rls, ConLeche.checkIotaRules μ (ConLeche.fueledOps μ F)
        env' envSelf fP cvNameP lpsP tyAP mI rP j rsP = .ok rls ∧
        Frontend.denoteRules st x = some rls) := by
  sorry

/-! ## The member checks -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
A member's header checked against its `_model` counterpart.

`sorry`: `blockRenameTable_spec`, `checkConstantVal_bridge`
(`Bridge/Checker/Base.lean`, item 11 of task #97-P3-Checker's list — the whole
tier's single highest-value remaining proof), and `CoreSpec.knot`'s `defeq`. -/
theorem checkMemberVal_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (env' : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (cv : IConstantVal)
    (cvP : ConstantVal) :
    CSpec μ env fe'
      (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP ∧
        Frontend.denoteCV st cv = some cvP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st fe' = some env)
      (Arena.checkMemberVal μ blockNames fe' cv)
      (fun st x => ∃ F cvA, ConLeche.checkMemberVal (ConLeche.fueledOps μ F)
        blockNamesP env' cvP = .ok cvA ∧
        Frontend.denoteCV st x = some cvA) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
One member checked and installed at its real inductive kind.

`sorry`: `checkMemberVal_spec` and `IFEnv.push`'s two lemmas. -/
theorem checkIndMember_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (caps : IIndCaps) (capsP : IndCaps)
    (ci : IConstantInfo) (ciP : ConstantInfo) :
    CSpec μ env fe'
      (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP ∧
        Frontend.denoteCaps st caps = some capsP ∧
        Frontend.denoteCI st ci = some ciP ∧ denoteFEnv st fe' = some env)
      (Arena.checkIndMember μ blockNames caps fe' ci)
      (InstRel fe' (fun e => ∃ F, ConLeche.checkIndMember
        (ConLeche.fueledOps μ F) blockNamesP capsP env ciP = .ok e)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
`checkIndMembers` is task #97d-2's explicit recursion for con-leche's
`foldlM` over the non-recursor members (deviation 3's fifth item).

`sorry`: a list induction over `checkIndMember_spec` and `InstRel.trans`
(closed, `Bridge/Inductives/Rel.lean`). -/
theorem checkIndMembers_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (caps : IIndCaps) (capsP : IndCaps)
    (cis : List IConstantInfo) (cisP : List ConstantInfo) :
    CSpec μ env fe
      (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP ∧
        Frontend.denoteCaps st caps = some capsP ∧
        Frontend.denoteCIList st cis = some cisP ∧ denoteFEnv st fe = some env)
      (Arena.checkIndMembers μ blockNames caps fe cis)
      (InstRel fe (fun e => ∃ F,
        cisP.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ F)
          blockNamesP capsP) env = .ok e)) := by
  sorry

/-! ## The recursors -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
The recursors' headers checked and PROVISIONALLY installed (their rules may
mention each other, so they install as a group).

`sorry`: `checkMemberVal_spec` and `IFEnv.push`, over a list induction. -/
theorem provisionRecs_spec {μ : CheckMode} {env : Env} (feAcc : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (cis : List IConstantInfo)
    (cisP : List ConstantInfo) :
    CSpec μ env feAcc
      (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP ∧
        Frontend.denoteCIList st cis = some cisP ∧
        denoteFEnv st feAcc = some env)
      (Arena.provisionRecs μ blockNames feAcc cis)
      (fun st r => ∃ F envP recsP,
        ConLeche.provisionRecs (ConLeche.fueledOps μ F) blockNamesP env cisP
          = .ok (envP, recsP) ∧
        InstRel feAcc (fun e => e = envP) st r.1 ∧
        recsP.length = r.2.length) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
`installIndRecs` is the twin's explicit recursion for con-leche's inner fold:
each provisioned recursor's rules certified and the record installed.

`sorry`: `checkIotaRules_spec` and `IFEnv.push`, over a list induction. -/
theorem installIndRecs_spec {μ : CheckMode} {env : Env} (fe₂ feSelf acc : IFEnv)
    (env₂ envSelf envAcc : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cs : List (IConstantVal × Nat × Nat × List IRecRule))
    (csP : List (ConstantVal × Nat × Nat × List RecRule)) :
    CSpec μ env acc
      (fun st => RenameRel st tbl fP ∧ denoteFEnv st fe₂ = some env₂ ∧
        denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st acc = some envAcc ∧ denoteFEnv st acc = some env)
      (Arena.installIndRecs μ fe₂ feSelf tbl acc cs)
      (InstRel acc (fun _ => csP.length = cs.length)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
The recursor group: the pinned `Eq` basis, the provisioning, the rename table
and the certified installs.

`sorry`: `eqBasisStored_spec`, `provisionRecs_spec`, `blockRenameTable_spec`
and `installIndRecs_spec`. -/
theorem checkIndRecs_spec {μ : CheckMode} {env : Env} (fe₂ : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (recs : List IConstantInfo)
    (recsP : List ConstantInfo) :
    CSpec μ env fe₂
      (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP ∧
        Frontend.denoteCIList st recs = some recsP ∧
        denoteFEnv st fe₂ = some env)
      (Arena.checkIndRecs μ blockNames fe₂ recs)
      (InstRel fe₂ (fun e => ∃ F, ConLeche.checkIndRecs
        μ (ConLeche.fueledOps μ F) blockNamesP env recsP = .ok e)) := by
  sorry

/-! ## The projection functions -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
The model's projection and the block's constructor, looked up.

**CLOSED** (task #97-P3-Ind round 7): `IFEnvOK`'s `hit` clause at the
constructor, the model projection and the parent, its `miss` clause at the
projection's own name, `projModelName_run`/`projFnName_run`, and
`eqBasisStored_spec` for the pinned-`Eq` guard. -/
theorem checkProjLookups_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF i : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.checkProjLookups fe' T ctorName lps nP nF i)
      (fun st r => ∃ a b, @ConLeche.checkProjLookups CheckM _ _ env TP
          ctorNameP lpsP nP nF i = .ok (a, b) ∧
        Frontend.denoteCV st r.1 = some a ∧ Frontend.denoteCV st r.2 = some b) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hC, hlps, hfe⟩ := hpre
  simp only [Arena.checkProjLookups] at hrun
  cases hf1 : fe'.find? ctorName with
  | none => rw [hf1] at hrun; exact absurd hrun (fun h => failOk h)
  | some ci =>
  rw [hf1] at hrun
  obtain ⟨nm1, c1, hnm1, hci1, henv1⟩ := hok.ienv.hit ctorName ci hf1
  obtain rfl : nm1 = ctorNameP := Option.some.inj (hnm1.symm.trans hC)
  cases ci
  case ctorInfo cvj cnP cnF =>
    obtain ⟨cvjP, rfl, hcvj⟩ := denoteCI_ctor_inv hci1
    dsimp only at hrun
    split at hrun
    case isFalse => obtain ⟨_, _, k, _⟩ := bindOk hrun; exact absurd k (fun h => failOk h)
    case isTrue har =>
    replace hrun := AM.pure_bind_ok hrun
    obtain ⟨h2, s2, k2, z2⟩ := bindOk hrun
    obtain ⟨p2, hh2⟩ := projModelName_run hok.state hT k2
    have c2 := p2.toCore hok
    cases hf2 : fe'.find? h2 with
    | none => rw [hf2] at z2; exact absurd z2 (fun h => failOk h)
    | some ci2 =>
    rw [hf2] at z2
    obtain ⟨nm2, c2P, hnm2, hci2, henv2⟩ := c2.ok.ienv.hit h2 ci2 hf2
    obtain rfl : nm2 = ConLeche.projModelName TP i := Option.some.inj (hnm2.symm.trans hh2)
    cases ci2
    case defnInfo mcv mv mh =>
      obtain ⟨mcvP, mvP, rfl, hmcv, -⟩ := denoteCI_defn_inv hci2
      dsimp only at z2
      split at z2
      case isFalse => obtain ⟨_, _, k, _⟩ := bindOk z2; exact absurd k (fun h => failOk h)
      case isTrue hlp =>
      replace z2 := AM.pure_bind_ok z2
      obtain ⟨h3, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hh3⟩ := projFnName_run c2.ok.state (denoteN_ext hT c2.ext) k3
      have c3 := c2.trans (p3.toCore c2.ok)
      split at z3
      case isFalse => obtain ⟨_, _, k, _⟩ := bindOk z3; exact absurd k (fun h => failOk h)
      case isTrue hnone =>
      replace z3 := AM.pure_bind_ok z3
      have hf3 : fe'.find? h3 = none := by simpa using hnone
      have henv3 := IFEnvOK.miss c3.ok.state c3.ok.ienv hh3 hf3
      split at z3
      case isFalse => obtain ⟨_, _, k, _⟩ := bindOk z3; exact absurd k (fun h => failOk h)
      case isTrue hsome =>
      replace z3 := AM.pure_bind_ok z3
      obtain ⟨ciT, hfT⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨nmT, cT, hnmT, -, henvT⟩ := c3.ok.ienv.hit T ciT hfT
      obtain rfl : nmT = TP := Option.some.inj (hnmT.symm.trans (denoteN_ext hT c3.ext))
      obtain ⟨b, s4, k4, z4⟩ := bindOk z3
      obtain ⟨c4, hb⟩ := eqBasisStored_spec fe' s3 s4 b c3.ok (denoteFEnv_ext c3.ext hfe) k4
      obtain ⟨hbt, z5⟩ := AM.dunless_ok AM.Never.fail_any z4
      replace z5 := AM.pure_bind_ok z5
      obtain ⟨rfl, rfl⟩ := pureOk z5
      have hbt' : decide (env.find? ConLeche.eqName = some ConLeche.eqA) = true := by
        rw [← hb]; exact hbt
      have c34 := c3.trans c4
      have hlpP : mcvP.levelParams = lpsP := by
        have e1 := denoteCV_lps hmcv
        rw [hlp] at e1
        exact Option.some.inj ((denoteNListE_ext (c2.ext) _ _ hlps).symm.trans e1) |>.symm
      refine ⟨c34, cvjP, mcvP, ?_, ?_, ?_⟩
      · simp only [ConLeche.checkProjLookups, henv1, henv2, henv3, henvT, hlpP, har,
          of_decide_eq_true hbt']
        rfl
      · exact denoteCV_ext hcvj c34.ext
      · exact denoteCV_ext hmcv (p3.ext.trans c4.ext)
    all_goals exact absurd z2 (fun h => failOk h)
  all_goals exact absurd hrun (fun h => failOk h)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:497-511 checkProjTy
The projection function's generated type.

`sorry`: `structProjResidP_spec`, `structFam_spec` and `mkPisOf_spec`. -/
theorem checkProjTy_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (mty : EIdx) (mtyP : Expr) (nP nF : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st mty = some mtyP ∧ denoteFEnv st fe' = some env)
      (Arena.checkProjTy fe' T ctorName lps mty nP nF)
      (fun st r => ∃ v, @ConLeche.checkProjTy CheckM _ _ env TP ctorNameP
          lpsP mtyP nP nF = .ok v ∧ denoteE st r = some v) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
The projection function's iota certificate.

`sorry`: `projBack_spec`/`projFwd_spec`, `domsMatchRenamed_spec`,
`eqApp3?_spec` and `CoreSpec.knot`'s `defeq` slot. -/
theorem checkProjIota_spec {μ : CheckMode} {env : Env} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (cvj : IConstantVal) (cvjP : ConstantVal)
    (nP nF i : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        Frontend.denoteCV st cvj = some cvjP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st fe' = some env)
      (Arena.checkProjIota μ fe' feSelf T ctorName lps cvj nP nF i)
      (fun _ _ => ∃ F, ConLeche.checkProjIota μ (ConLeche.fueledOps μ F) env'
        envSelf TP ctorNameP lpsP cvjP nP nF i = .ok ()) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
One projection function checked and installed.

`sorry`: `checkProjLookups_spec`, `checkProjTy_spec`, `checkProjIota_spec`,
`CoreSpec.knot`'s `defeq` slot and `IFEnv.push`. -/
theorem checkProjFn_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T ctorName : NIdx)
    (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF i : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.checkProjFn μ fe' T ctorName lps nP nF i)
      (InstRel fe' (fun e => ∃ F, ConLeche.checkProjFn
        μ (ConLeche.fueledOps μ F) env TP ctorNameP lpsP nP nF i = .ok e)) := by
  sorry

/-! ## The capability theorems -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
Is the block's eta theorem stored with the pinned statement?  PURE on
con-leche's side (a `Bool`), monadic here because the comparison reads the
store.

`sorry`: `IFEnvOK`'s `hit` clause, `internNNode_spec` at the theorem's name,
and `denoteE_inj` at the statement comparison. -/
theorem checkEtaThm_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.checkEtaThm μ fe' T ctorName lps nP nF)
      (RV (ConLeche.checkEtaThm μ env TP ctorNameP lpsP nP nF)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
The unit-likeness theorem, the same way.

`sorry`: as `checkEtaThm_spec`. -/
theorem checkUnitThm_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.checkUnitThm μ fe' T lps nP)
      (RV (ConLeche.checkUnitThm μ env TP lpsP nP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:682-710 ctorTargetsFam
Does the constructor return the family?  The structure-like test the
projection install is gated on.

**PROVED** (round 4): `stripPis_pstep` with its two-sided inversion,
`structFam_spec` (closed) and `beq_ehandle_eq` — this tier's second cash of
`denoteE_inj`, at the one comparison the gate makes. -/
theorem ctorTargetsFam_spec (ctorTy : EIdx) (ctorTyP : Expr) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nF : Nat) :
    PSpec (fun st => denoteE st ctorTy = some ctorTyP ∧
        denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.ctorTargetsFam ctorTy T lps nP nF)
      (RV (ConLeche.ctorTargetsFam ctorTyP TP lpsP nP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hcty, hT, hlps⟩ := hpre
  simp only [Arena.ctorTargetsFam] at hrun
  obtain ⟨sp, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hcty h1
  cases sp with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨PStep.refl hok, ?_⟩
    simp only [RV, ConLeche.ctorTargetsFam, stripPis_none hbp]
  | some p =>
    obtain ⟨cbs, cbody⟩ := p
    obtain ⟨xs, x, hsp, hx⟩ := stripPis_some hbp
    obtain ⟨fam, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨hstep, hfam⟩ :=
      structFam_spec T TP lps lpsP nP nF _ s₂ fam hok ⟨hT, hlps⟩ h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨hstep, ?_⟩
    simp only [RV, ConLeche.ctorTargetsFam, hsp]
    exact beq_ehandle_eq hstep.ok.wf (denote_ext hx hstep.ext) hfam

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:712-722 installProjFnStep
One projection install, with its duplicate guard.

`sorry`: `checkProjFn_spec` and `IFEnvOK`'s `miss` clause. -/
theorem installProjFnStep_spec {μ : CheckMode} {env : Env} (e : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T ctorName : NIdx)
    (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF i : Nat) :
    CSpec μ env e
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st e = some env)
      (Arena.installProjFnStep μ T ctorName lps nP nF e i)
      (InstRel e (fun x => ∃ F, ConLeche.installProjFnStep
        μ (ConLeche.fueledOps μ F) TP ctorNameP lpsP nP nF env i = .ok x)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
`installProjFns` is the twin's explicit recursion for con-leche's third
`foldlM` (deviation 3).

`sorry`: a `Nat` recursion over `installProjFnStep_spec` and `InstRel.trans`. -/
theorem installProjFns_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (T ctorName : NIdx)
    (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF k i : Nat) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe = some env)
      (Arena.installProjFns μ T ctorName lps nP nF fe k i)
      (InstRel fe (fun x => ∃ F,
        (List.range k).foldlM (fun e j => ConLeche.installProjFnStep
          μ (ConLeche.fueledOps μ F) TP ctorNameP lpsP nP nF e (i + j)) env
          = .ok x)) := by
  sorry

/-! ## The capability record and the route -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:724-735 indBlockCaps
The block's capability record: eta and unit-likeness off the two theorems,
rule K off the shape.

`sorry`: `checkEtaThm_spec`, `checkUnitThm_spec` and `Frontend.denoteCaps` at
the answer. -/
theorem indBlockCaps_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (cvT cvC : IConstantVal) (cvTP cvCP : ConstantVal) (nP nF : Nat) :
    CSpec μ env fe
      (fun st => Frontend.denoteCV st cvT = some cvTP ∧
        Frontend.denoteCV st cvC = some cvCP ∧ denoteFEnv st fe = some env)
      (Arena.indBlockCaps μ fe cvT cvC nP nF)
      (RCaps (ConLeche.indBlockCaps μ env cvTP cvCP nP nF)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
The eta capability's constructor returns the family (task #136).

**CLOSED** (task #97-P3-Ind round 5): the capability guard, `IFEnvOK`'s
`hit`/`miss` pair at the stored constructor — the check reads the constant the
way its consumers do, which is what makes the `find?` load-bearing —
`stripPis_pstep`, `structFam_spec` and `beq_ehandle_eq`.  The six
non-constructor kinds close on `denoteCI_not_ctor`: `denoteCI` preserves the
kind, so the arena's fallthrough arm and con-leche's are the same arm. -/
theorem ctorResidualOk_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) (eta : Bool) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.ctorResidualOk μ fe' T ctorName lps nP nF eta)
      (RV (ConLeche.ctorResidualOk μ env TP ctorNameP lpsP nP nF eta)) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hT, hct, hlps, _⟩ := hpre
  simp only [Arena.ctorResidualOk] at hrun
  split at hrun
  case isTrue hg =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hck, ?_⟩
    show (true : Bool) = _
    simp only [ConLeche.ctorResidualOk, hg]
    simp
  case isFalse hg =>
    have hg' : (!μ.ttChecks || !eta) = false := by
      simp only [Bool.not_eq_true] at hg; exact hg
    cases hf : fe'.find? ctorName with
    | none =>
      rw [hf] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨CoreStep.refl hck, ?_⟩
      show (false : Bool) = _
      have hmiss : env.find? ctorNameP = none :=
        IFEnvOK.miss hck.state hck.ienv hct hf
      simp only [ConLeche.ctorResidualOk, hg', hmiss]
      simp
    | some ci =>
      obtain ⟨nm, c, hnm, hci, henv⟩ := hck.ienv.hit ctorName ci hf
      obtain rfl := Option.some.inj (hnm.symm.trans hct)
      cases ci
      case ctorInfo cvCA nP' nF' =>
        simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
        obtain ⟨cvP, hcv, rfl⟩ := hci
        rw [hf] at hrun
        obtain ⟨sq, s1, k1, hrun2⟩ := bindOk hrun
        obtain ⟨hs1, hsq⟩ := stripPis_pstep hck.state (denoteCV_type hcv) k1
        rw [hs1] at hrun2
        rcases sq with _ | ⟨sbs, sbody⟩
        · obtain ⟨rfl, rfl⟩ := pureOk hrun2
          refine ⟨CoreStep.refl hck, ?_⟩
          show (false : Bool) = _
          simp only [ConLeche.ctorResidualOk, hg', henv, stripPis_none hsq]
          simp
        obtain ⟨sxs, sbodyP, hsps, _, hsbody⟩ := denoteBP_someB hsq
        obtain ⟨fam, s2, k2, hrun3⟩ := bindOk hrun2
        obtain ⟨p2, hfam⟩ :=
          structFam_spec T TP lps lpsP nP nF s₀ s2 fam hck.state ⟨hT, hlps⟩ k2
        obtain ⟨rfl, rfl⟩ := pureOk hrun3
        refine ⟨p2.toCore hck, ?_⟩
        show (sbody == fam) = _
        simp only [ConLeche.ctorResidualOk, hg', henv, hsps]
        rw [beq_ehandle_eq p2.ok.wf (denote_ext hsbody p2.ext) hfam]
        simp
      all_goals
        (rw [hf] at hrun
         obtain ⟨rfl, rfl⟩ := pureOk hrun
         refine ⟨CoreStep.refl hck, ?_⟩
         show (false : Bool) = _
         have hne := denoteCI_not_ctor hci (by simp)
         simp only [ConLeche.ctorResidualOk, hg', henv]
         cases c
         case ctorInfo v n1 n2 => exact absurd rfl (hne v n1 n2)
         all_goals simp)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
**THE MODELED ROUTE**, the second of `checkIndDecl`'s two dispatches: every
member checked against its `_model` counterpart, the recursors installed as a
group, and — at a structure-like block — the projection functions.

`sorry`: `indBlockCaps_spec`, `checkIndMembers_spec`, `checkIndRecs_spec`,
`ctorResidualOk_spec`, `ctorTargetsFam_spec`, `installProjFns_spec`, and
`recsFormSuffix`/`isRecInfo`'s exactness (both tag reads, so both are
`Frontend.denoteCI`'s case split). -/
theorem checkModeled_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (block : List IConstantInfo)
    (blockP : List ConstantInfo) :
    CSpec μ env fe
      (fun st => Frontend.denoteCIList st block = some blockP ∧
        denoteFEnv st fe = some env)
      (Arena.checkModeled μ fe block)
      (InstRel fe (fun e => ∃ F, ConLeche.checkModeled μ
        (ConLeche.fueledOps μ F) env blockP = .ok e)) := by
  sorry

end ConRon.Bridge.Inductives

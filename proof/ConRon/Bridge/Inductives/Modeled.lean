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
import ConLeche.Verify.Extend.Iota
import ConLeche.Verify.Extend.Modeled
import ConRon.Bridge.Frontend.Lines

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

/-- con-leche: none — **a rename relation at every well-formed extension**
(task #97-P3-Ind round 8): the form the iota family needs, because its
renaming walks run at stores the certificate's earlier steps have grown, and
`RenameRel` is not monotone in general (round 7's R7.5).  The two builders
supply it (`blockRenameTable_specW`, `projBack_specW`/`projFwd_specW`). -/
def RenameRelW (st : EStore) (tbl : List (NIdx × NIdx))
    (f : ConLeche.Name → ConLeche.Name) : Prop :=
  ∀ st' : EStore, Ext st st' → StoreWF st' → RenameRel st' tbl f

theorem RenameRelW.mono {st st' : EStore} {tbl : List (NIdx × NIdx)}
    {f : ConLeche.Name → ConLeche.Name} (h : RenameRelW st tbl f) (hx : Ext st st') :
    RenameRelW st' tbl f :=
  fun st'' hx' hwf => h st'' (hx.trans hx') hwf

theorem RenameRelW.now {st : EStore} {tbl : List (NIdx × NIdx)}
    {f : ConLeche.Name → ConLeche.Name} (h : RenameRelW st tbl f) (hwf : StoreWF st) :
    RenameRel st tbl f :=
  h st (Ext.refl _) hwf

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

/-- con-leche: none — `blockRenameTable_spec` at every well-formed extension
of the final store (task #97-P3-Ind round 8, as round 7's `projBack_specW`):
`checkMemberVal` builds the table FIRST and renames only after
`checkConstantVal` has grown the arena.  A handle new at the extension cannot
denote a block name the table knows (`denoteN_inj` there), so the table's
lookups are the same. -/
theorem blockRenameTable_specW (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) :
    PSpec (fun st => Frontend.denoteNList st.ns blockNames = some blockNamesP)
      (Arena.blockRenameTable blockNames)
      (fun st r => ∀ st' : EStore, Ext st st' → StoreWF st' → RenameRel st' r
        (fun n => if blockNamesP.contains n then n.str "_model" else n)) := by
  induction blockNames generalizing blockNamesP with
  | nil =>
    intro s₀ s' r hok hd hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.blockRenameTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    intro st' _ _ q qm hq
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
        intro st' hxt hwf' q qm hq
        have hn' : denoteN st'.ns n = some nm :=
          denoteN_ext (denoteN_ext (denoteN_ext hn hstep1.ext) hstep2.ext) hxt
        have hm' : denoteN st'.ns m = some (nm.str "_model") :=
          denoteN_ext (denoteN_ext hm hstep2.ext) hxt
        have hbq := beq_handle_eq hwf' hn' hq
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
          have hrec := hrel st' hxt hwf' q qm hq
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

/-- con-leche: none — `projBackGo_run` at EVERY well-formed extension of its
final store (task #97-P3-Ind round 7): the table's keys denote, so
`denoteN_inj` pins any later handle of a key's name to the key. -/
theorem projBackGo_runW (T : NIdx) (TP : ConLeche.Name) :
    ∀ (k j : Nat) {s s' : AState} {r : List (NIdx × NIdx)},
      StateOK s → denoteN s.store.ns T = some TP →
      Arena.projBack.go T k j s = .ok (r, s') →
      PStep s s' ∧ ∀ (st' : EStore), Ext s'.store st' → StoreWF st' →
        ∀ (n : NIdx) (nm : ConLeche.Name), denoteN st'.ns n = some nm →
        denoteN st'.ns (Arena.renameBy r n) =
          some (projBackTail TP k j nm) := by
  intro k
  induction k with
  | zero =>
    intro j s s' r hok hT hrun
    simp only [Arena.projBack.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, fun st' _ _ n nm hn => by
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
    intro st' hxt hwf n nm hn
    have ha' : denoteN st'.ns a = some (ConLeche.projModelName TP j) :=
      denoteN_ext (denoteN_ext (denoteN_ext ha p2.ext) p3.ext) hxt
    have hb' : denoteN st'.ns b = some (ConLeche.projFnName TP j) :=
      denoteN_ext (denoteN_ext hb p3.ext) hxt
    rw [renameBy_cons, beq_handle_eq' hwf ha' hn]
    simp only [projBackTail]
    split
    · exact hb'
    · exact hx st' hxt hwf n nm hn

/-- con-leche: none — `projFwdGo_run` at EVERY well-formed extension of its
final store (task #97-P3-Ind round 7): the table's keys denote, so
`denoteN_inj` pins any later handle of a key's name to the key. -/
theorem projFwdGo_runW (T : NIdx) (TP : ConLeche.Name) :
    ∀ (k j : Nat) {s s' : AState} {r : List (NIdx × NIdx)},
      StateOK s → denoteN s.store.ns T = some TP →
      Arena.projFwd.go T k j s = .ok (r, s') →
      PStep s s' ∧ ∀ (st' : EStore), Ext s'.store st' → StoreWF st' →
        ∀ (n : NIdx) (nm : ConLeche.Name), denoteN st'.ns n = some nm →
        denoteN st'.ns (Arena.renameBy r n) =
          some (projFwdTail TP k j nm) := by
  intro k
  induction k with
  | zero =>
    intro j s s' r hok hT hrun
    simp only [Arena.projFwd.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, fun st' _ _ n nm hn => by
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
    intro st' hxt hwf n nm hn
    have ha' : denoteN st'.ns a = some (ConLeche.projFnName TP j) :=
      denoteN_ext (denoteN_ext (denoteN_ext ha p2.ext) p3.ext) hxt
    have hb' : denoteN st'.ns b = some (ConLeche.projModelName TP j) :=
      denoteN_ext (denoteN_ext hb p3.ext) hxt
    rw [renameBy_cons, beq_handle_eq' hwf ha' hn]
    simp only [projFwdTail]
    split
    · exact hb'
    · exact hx st' hxt hwf n nm hn

/-- con-leche: none — `projBack_spec` at every well-formed extension (round 7). -/
theorem projBack_specW (T ctor : NIdx) (TP ctorP : ConLeche.Name) (nF : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns ctor = some ctorP)
      (Arena.projBack T ctor nF)
      (fun st r => ∀ st' : EStore, Ext st st' → StoreWF st' → RenameRel st' r (ConLeche.projBack TP ctorP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hct⟩ := hpre
  simp only [Arena.projBack] at hrun
  obtain ⟨tm, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok hT k1
  obtain ⟨cm, s2, k2, h3⟩ := bindOk h2
  obtain ⟨p2, hcm⟩ := internStrN_run p1.ok (denoteN_ext hct p1.ext) k2
  obtain ⟨x, s3, k3, h4⟩ := bindOk h3
  obtain ⟨p3, hx⟩ := projBackGo_runW T TP nF 0 p2.ok
    (denoteN_ext hT (p1.ext.trans p2.ext)) k3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨p1.trans (p2.trans p3), ?_⟩
  intro st' hxt hwf n nm hn
  have htm' : denoteN st'.ns tm = some (TP.str "_model") :=
    denoteN_ext (denoteN_ext (denoteN_ext htm p2.ext) p3.ext) hxt
  have hcm' : denoteN st'.ns cm = some (ctorP.str "_model") :=
    denoteN_ext (denoteN_ext hcm p3.ext) hxt
  have hT' : denoteN st'.ns T = some TP :=
    denoteN_ext hT ((p1.ext.trans (p2.ext.trans p3.ext)).trans hxt)
  have hct' : denoteN st'.ns ctor = some ctorP :=
    denoteN_ext hct ((p1.ext.trans (p2.ext.trans p3.ext)).trans hxt)
  show denoteN st'.ns (Arena.renameBy _ n) =
    some (ConLeche.projBack TP ctorP nF nm)
  rw [renameBy_cons, renameBy_cons,
    beq_handle_eq' hwf htm' hn, beq_handle_eq' hwf hcm' hn]
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
      rw [hx st' hxt hwf n nm hn, projBackTail_eq TP nF 0 nm, List.range_eq_range']
      rfl

/-- con-leche: none — `projFwd_spec` at every well-formed extension (round 7). -/
theorem projFwd_specW (T ctor : NIdx) (TP ctorP : ConLeche.Name) (nF : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns ctor = some ctorP)
      (Arena.projFwd T ctor nF)
      (fun st r => ∀ st' : EStore, Ext st st' → StoreWF st' → RenameRel st' r (ConLeche.projFwd TP ctorP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hct⟩ := hpre
  simp only [Arena.projFwd] at hrun
  obtain ⟨tm, s1, k1, h2⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok hT k1
  obtain ⟨cm, s2, k2, h3⟩ := bindOk h2
  obtain ⟨p2, hcm⟩ := internStrN_run p1.ok (denoteN_ext hct p1.ext) k2
  obtain ⟨x, s3, k3, h4⟩ := bindOk h3
  obtain ⟨p3, hx⟩ := projFwdGo_runW T TP nF 0 p2.ok
    (denoteN_ext hT (p1.ext.trans p2.ext)) k3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨p1.trans (p2.trans p3), ?_⟩
  intro st' hxt hwf n nm hn
  have htm' : denoteN st'.ns tm = some (TP.str "_model") :=
    denoteN_ext (denoteN_ext (denoteN_ext htm p2.ext) p3.ext) hxt
  have hcm' : denoteN st'.ns cm = some (ctorP.str "_model") :=
    denoteN_ext (denoteN_ext hcm p3.ext) hxt
  have hT' : denoteN st'.ns T = some TP :=
    denoteN_ext hT ((p1.ext.trans (p2.ext.trans p3.ext)).trans hxt)
  have hct' : denoteN st'.ns ctor = some ctorP :=
    denoteN_ext hct ((p1.ext.trans (p2.ext.trans p3.ext)).trans hxt)
  show denoteN st'.ns (Arena.renameBy _ n) =
    some (ConLeche.projFwd TP ctorP nF nm)
  rw [renameBy_cons, renameBy_cons,
    beq_handle_eq' hwf hT' hn, beq_handle_eq' hwf hct' hn]
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
      rw [hx st' hxt hwf n nm hn, projFwdTail_eq TP nF 0 nm, List.range_eq_range']
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

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
The pinned-`Eq` guard at `ReadOK` (task #97-P3-Ind round 8): it reads the
index and the pins and interns, but touches no cache. -/
theorem eqBasisStored_run {env : Env} (fe : IFEnv) :
    ∀ (s₀ s' : AState) (r : Bool), ReadOK env fe s₀ →
      Arena.eqBasisStored fe s₀ = .ok (r, s') →
      InstStep s₀ s' ∧ r = decide (env.find? ConLeche.eqName = some ConLeche.eqA) := by
  intro s₀ s' r hok hrun
  simp only [Arena.eqBasisStored] at hrun
  obtain ⟨n, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hn⟩ := pinAt_run (x := ConLeche.eqName) hok.pins rfl k1
  rw [hs1] at z1
  cases hf : fe.find? n with
  | none =>
    rw [hf] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨InstStep.refl hok.state, ?_⟩
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
  refine ⟨⟨hstep.ok, hstep.ext, hstep.pins⟩, ?_⟩
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

/-- con-leche: none — **`eqApp3?`'s `none` half** (task #97-P3-Ind round 7):
a `none` answer means the subject is NOT an `Eq`-shaped triple application,
so con-leche's `match` falls through to its `_` arm too.  `eqApp3?_spec` is
the `some` half; the capability theorems read both. -/
theorem eqApp3?_none (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP)
      (Arena.eqApp3? h)
      (fun _ r => r = none → ∀ c u ty l rr,
        hP ≠ .app (.app (.app (.const c [u]) ty) l) rr) := by
  intro s₀ s' r hok hd hrun
  have hwf := hok.wf
  simp only [Arena.eqApp3?] at hrun
  obtain ⟨v1, s1, g1, k1⟩ := bindOk hrun
  obtain ⟨rfl, hw1⟩ := view_run g1
  cases v1
  case app f1 rr =>
    obtain ⟨efP, errP, rfl, hf1, hrr⟩ := denote_app_inv hwf hw1 hd
    obtain ⟨v2, s2, g2, k2⟩ := bindOk k1
    obtain ⟨rfl, hw2⟩ := view_run g2
    cases v2
    case app f2 l =>
      obtain ⟨ef2P, elP, rfl, hf2, hl⟩ := denote_app_inv hwf hw2 hf1
      obtain ⟨v3, s3, g3, k3⟩ := bindOk k2
      obtain ⟨rfl, hw3⟩ := view_run g3
      cases v3
      case app f3 ty =>
        obtain ⟨ef3P, etyP, rfl, hf3, hty⟩ := denote_app_inv hwf hw3 hf2
        obtain ⟨v4, s4, g4, k4⟩ := bindOk k3
        obtain ⟨rfl, hw4⟩ := view_run g4
        cases v4
        case const c us =>
          obtain ⟨cP, lsP, rfl, hc, hus⟩ := denote_const_inv hwf hw4 hf3
          obtain ⟨vs, s5, g5, k5⟩ := bindOk k4
          obtain ⟨rfl, hw5⟩ := viewLs_run g5
          have hvs := denoteLs_of_view hw5 hus
          refine ⟨?_, ?_⟩
          · cases vs with
            | nil => obtain ⟨rfl, rfl⟩ := pureOk k5; exact PStep.refl hok
            | cons a t =>
              cases t with
              | nil => obtain ⟨rfl, rfl⟩ := pureOk k5; exact PStep.refl hok
              | cons _ _ => obtain ⟨rfl, rfl⟩ := pureOk k5; exact PStep.refl hok
          · intro hr c' u ty' l' rr' heq
            simp only [Expr.app.injEq, Expr.const.injEq] at heq
            obtain ⟨⟨⟨⟨-, rfl⟩, -⟩, -⟩, -⟩ := heq
            cases vs with
            | nil =>
              simp [denoteLList] at hvs
            | cons a t =>
              cases t with
              | nil =>
                obtain ⟨rfl, rfl⟩ := pureOk k5
                simp at hr
              | cons b t' =>
                have := denoteLList_length _ _ hvs
                simp at this
        all_goals
          (obtain ⟨rfl, rfl⟩ := pureOk k4
           refine ⟨PStep.refl hok, fun _ c' u ty' l' rr' heq => ?_⟩
           simp only [Expr.app.injEq] at heq
           obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := heq
           rw [denoteE_view_eq hwf hw4] at hf3
           simp [denoteEView] at hf3)
      all_goals
        (obtain ⟨rfl, rfl⟩ := pureOk k3
         refine ⟨PStep.refl hok, fun _ c' u ty' l' rr' heq => ?_⟩
         simp only [Expr.app.injEq] at heq
         obtain ⟨⟨rfl, -⟩, -⟩ := heq
         rw [denoteE_view_eq hwf hw3] at hf2
         simp [denoteEView] at hf2)
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk k2
       refine ⟨PStep.refl hok, fun _ c' u ty' l' rr' heq => ?_⟩
       simp only [Expr.app.injEq] at heq
       obtain ⟨rfl, -⟩ := heq
       rw [denoteE_view_eq hwf hw2] at hf1
       simp [denoteEView] at hf1)
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk k1
     refine ⟨PStep.refl hok, fun _ c' u ty' l' rr' heq => ?_⟩
     subst heq
     rw [denoteE_view_eq hwf hw1] at hd
     simp [denoteEView] at hd)

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
theorem checkIotaThm_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF envSelf)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) (cvj : IConstantVal) (cvjP : ConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (rhsAP : Expr) :
    CSpec μ envSelf feSelf
      (fun st => RenameRelW st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        Frontend.denoteCV st cvj = some cvjP ∧ denoteE st rhsA = some rhsAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
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
theorem nestedRuleShape_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (cvName : NIdx) (cvNameP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr)
    (mI rP cnP j : Nat) :
    CSpec μ envSelf feSelf
      (fun st => denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
      (Arena.nestedRuleShape fe' feSelf cvName lps tyA mI rP cnP j)
      (ROp (fun q st r => denoteLList st.ls r.1 = some q.1 ∧
          Frontend.denoteEList st r.2 = some q.2)
        (ConLeche.nestedRuleShape env' envSelf cvNameP lpsP tyAP mI rP cnP j)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
**The nested iota certificate**, which also decides the rule's firing mode.

`sorry`: `nestedRuleShape_spec`, `checkIotaThm_spec`'s pieces, and
`Frontend.denoteFire` at the answer. -/
theorem checkIotaThmN_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF envSelf)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) (cvj : IConstantVal) (cvjP : ConstantVal)
    (cnP cnF : Nat) (rhsA : EIdx) (rhsAP : Expr) :
    CSpec μ envSelf feSelf
      (fun st => RenameRelW st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        Frontend.denoteCV st cvj = some cvjP ∧ denoteE st rhsA = some rhsAP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
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
theorem checkIotaRule_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF envSelf)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (r : IRecRule) (rP' : RecRule) :
    CSpec μ envSelf feSelf
      (fun st => RenameRelW st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRule st r = some rP' ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
      (Arena.checkIotaRule μ fe' feSelf tbl cvName lps tyA mI rP j r)
      (fun st x => ∃ F rl, ConLeche.checkIotaRule μ (ConLeche.fueledOps μ F)
        env' envSelf fP cvNameP lpsP tyAP mI rP j rP' = .ok rl ∧
        Frontend.denoteRule st x = some rl) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:362-371 checkIotaRules
The whole rule list.

`sorry`: a list induction over `checkIotaRule_spec`. -/
theorem checkIotaRules_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF envSelf)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cvName : NIdx) (cvNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP j : Nat)
    (rs : List IRecRule) (rsP : List RecRule) :
    CSpec μ envSelf feSelf
      (fun st => RenameRelW st tbl fP ∧ denoteN st.ns cvName = some cvNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP ∧ Frontend.denoteRules st rs = some rsP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
      (Arena.checkIotaRules μ fe' feSelf tbl cvName lps tyA mI rP j rs)
      (fun st x => ∃ F rls, ConLeche.checkIotaRules μ (ConLeche.fueledOps μ F)
        env' envSelf fP cvNameP lpsP tyAP mI rP j rsP = .ok rls ∧
        Frontend.denoteRules st x = some rls) := by
  induction rs generalizing j rsP with
  | nil =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨-, -, -, -, hrs, -⟩ := hpre
    simp only [Frontend.denoteRules, Option.some.injEq] at hrs
    subst hrs
    simp only [Arena.checkIotaRules] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hck, 0, [], rfl, rfl⟩
  | cons rl rest ih =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨hren, hcn, hlps, hty, hrs, hfe', hfeS, hok'⟩ := hpre
    simp only [Frontend.denoteRules] at hrs
    cases hr1 : Frontend.denoteRule s₀.store rl with
    | none => rw [hr1] at hrs; simp at hrs
    | some rlP =>
    cases hr2 : Frontend.denoteRules s₀.store rest with
    | none => rw [hr1, hr2] at hrs; simp at hrs
    | some restP =>
    rw [hr1, hr2] at hrs
    obtain rfl := (Option.some.inj hrs).symm
    simp only [Arena.checkIotaRules] at hrun
    obtain ⟨r1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, F₁, rl', hF₁, hrl'⟩ := checkIotaRule_spec fe' feSelf env' envSelf hk henv tbl fP
      cvName cvNameP lps lpsP tyA tyAP mI rP j rl rlP s₀ s₁ r1 hck
      ⟨hren, hcn, hlps, hty, hr1, hfe', hfeS, hok'⟩ k1
    have x1 := c1.ext
    obtain ⟨r2, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨c2, F₂, rls, hF₂, hrls⟩ := ih (j + 1) restP s₁ s₂ r2 c1.ok
      ⟨hren.mono x1, denoteN_ext hcn x1, denoteNListE_ext x1 _ _ hlps, denote_ext hty x1,
        denoteRules_ext x1 _ _ hr2, denoteFEnv_ext x1 hfe', denoteFEnv_ext x1 hfeS,
        hok'.mono x1⟩ k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, max F₁ F₂, rl' :: rls, ?_, ?_⟩
    · have g₁ : ConLeche.checkIotaRule μ (ConLeche.fueledOps μ (max F₁ F₂)) env' envSelf fP
          cvNameP lpsP tyAP mI rP j rlP = .ok rl' := by
        rw [← ConLeche.checkIotaRule_datF] at hF₁ ⊢
        exact (ConLeche.checkIotaRule μ (ConLeche.fueledOpsM μ) env' envSelf fP cvNameP lpsP
          tyAP mI rP j rlP).property (Nat.le_max_left F₁ F₂) hF₁
      have g₂ : ConLeche.checkIotaRules μ (ConLeche.fueledOps μ (max F₁ F₂)) env' envSelf fP
          cvNameP lpsP tyAP mI rP (j + 1) restP = .ok rls := by
        rw [← ConLeche.checkIotaRules_datF] at hF₂ ⊢
        exact (ConLeche.checkIotaRules μ (ConLeche.fueledOpsM μ) env' envSelf fP cvNameP lpsP
          tyAP mI rP (j + 1) restP).property (Nat.le_max_right F₁ F₂) hF₂
      simp only [ConLeche.checkIotaRules, bind, Except.bind, g₁, g₂, pure, Except.pure]
    · simp only [Frontend.denoteRules, denoteRule_ext hrl' c2.ext, hrls]

/-! ## The member checks -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
A member's header checked against its `_model` counterpart.

`sorry`: `blockRenameTable_spec`, `checkConstantVal_bridge`
(`Bridge/Checker/Base.lean`, item 11 of task #97-P3-Checker's list — the whole
tier's single highest-value remaining proof), and `CoreSpec.knot`'s `defeq`. -/
theorem checkMemberVal_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (env' : Env) (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (blockNames : List NIdx)
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
  intro s₀ s' r hck hpre hrun
  obtain ⟨hbn, hcv, hfe', hfe⟩ := hpre
  obtain rfl : env' = env := Option.some.inj (hfe'.symm.trans hfe)
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkMemberVal] at hrun
  -- the rename table
  obtain ⟨tbl, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, htbl⟩ := blockRenameTable_specW blockNames blockNamesP s₀ s₁ tbl hck.state
    hbn k1
  have c1 := p1.toCore hck
  -- the member's own check
  obtain ⟨cvA, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨c2, cAP, F, hcA, hF⟩ := checkConstantVal_bridge hμ hk c1.ok henv
    (denoteCV_ext hcv p1.ext) k2
  have c12 := c1.trans c2
  -- the model-shaped name guard
  obtain ⟨an, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨rfl, han⟩ := Frontend.readName_run k3
  have hnm := denoteCV_name hcA
  obtain rfl : an = cAP.name := Option.some.inj (han.symm.trans hnm)
  split at z3
  · exact absurd z3 (hnever _ _ _)
  rename_i hms
  replace z3 := AM.pure_bind_ok z3
  -- the model counterpart
  obtain ⟨mn, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hmn⟩ := internNNode_run c12.ok.state
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hnm) k4
  simp only [denoteNView, denoteN_ext hnm p4.ext, Option.map_some] at hmn
  have c14 := c12.trans (p4.toCore c12.ok)
  have hienv := c14.ok.ienv
  cases hf : fe'.find? mn with
  | none =>
    rw [hf] at z4
    exact absurd z4 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | some ci =>
  rw [hf] at z4
  obtain ⟨nm', cm, hnm', hcm, henvm⟩ := hienv.hit mn ci hf
  obtain rfl := Option.some.inj (hnm'.symm.trans hmn)
  cases ci
  case defnInfo cvm mval hint =>
    obtain ⟨cvmP, mvalP, rfl, hcvm, -⟩ := denoteCI_defn_inv hcm
    dsimp only at z4
    -- the level parameters
    obtain ⟨hlps, z5⟩ := AM.dunless_ok hnever z4
    replace z5 := AM.pure_bind_ok z5
    have hlpsP : cvmP.levelParams = cAP.levelParams := by
      have e1 := denoteCV_lps hcvm
      have e2 := denoteNListE_ext p4.ext _ _ (denoteCV_lps hcA)
      rw [hlps] at e1
      exact Option.some.inj (e1.symm.trans e2)
    -- the renamed type against the model's
    obtain ⟨ren, s₅, k5, z6⟩ := bindOk z5
    have x14 : Ext s₁.store s₄.store := c2.ext.trans p4.ext
    obtain ⟨p5, -, hren⟩ := renameConstsFast_pstep c14.ok.state
      (htbl s₄.store x14 c14.ok.state.wf) (denote_ext (denoteCV_type hcA) p4.ext) k5
    have c15 := c14.trans (p5.toCore c14.ok)
    have hbeq := beq_ehandle_eq c15.ok.state.wf hren
      (denote_ext (denoteCV_type hcvm) p5.ext)
    obtain ⟨hty, z7⟩ := AM.dunless_ok hnever z6
    replace z7 := AM.pure_bind_ok z7
    rw [hbeq] at hty
    obtain ⟨rfl, rfl⟩ := pureOk z7
    refine ⟨c15, F, cAP, ?_, denoteCV_ext hcA (p4.ext.trans p5.ext)⟩
    have hms' : cAP.name.isModelSuffix = false := by
      simpa using hms
    simp only [ConLeche.checkMemberVal, bind, Except.bind, hF, hms', Bool.false_eq_true,
      if_false, henvm, hlpsP, if_true, hty, pure, Except.pure]
  all_goals exact absurd z4 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:164 checkIndMemberS_run
(its `EnvWF` half, pure) — **one member step leaves a well-formed environment
and conses a fresh constant.**  The member is `checkMemberVal`'s checked
constant (`checkIndMember_inv`), its type closed and resolving
(`checkConstantVal_typeWF`); a former's capability arities are
`indCapsWF_of_pins` at the block's pins. -/
theorem checkIndMember_wf {μ : CheckMode} {F : Nat} {bn : List ConLeche.Name}
    {caps : IndCaps} {env e : Env} {ci : ConstantInfo} (henv : EnvWF env)
    (hpins : ∀ cv caps₀, ci = .indInfo cv caps₀ →
      ConLeche.EtaPins μ env cv.name cv.levelParams caps)
    (h : ConLeche.checkIndMember (ConLeche.fueledOps μ F) bn caps env ci = .ok e) :
    EnvWF e ∧ ∃ c, e = ⟨c :: env.consts⟩ ∧ env.find? c.name = none := by
  obtain ⟨cvA, cvm, mval, hint, hccv, -, hfm, -, hty, hkind⟩ := ConLeche.checkIndMember_inv h
  obtain ⟨htf, htp, htr, htb⟩ := ConLeche.checkConstantVal_typeWF hccv
  obtain ⟨hfresh, -, -, -, -, -, type, -, -, -, -, -, -, -, hcvA⟩ :=
    ConLeche.checkConstantVal_inv hccv
  rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
  · have hicw : ConLeche.IndCapsWF (.indInfo cvA caps) := by
      refine ConLeche.indCapsWF_of_pins (μ := μ) ?_ hfm hty
      rw [hcvA]
      exact hpins cv caps' rfl
    refine ⟨ConLeche.EnvWF.cons henv ⟨htf, htp, Expr.constsResolve_mono htr, htb,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq), hicw⟩, _, rfl, ?_⟩
    show env.find? cvA.name = none
    rw [hcvA]
    exact hfresh
  · refine ⟨ConLeche.EnvWF.cons henv ⟨htf, htp, Expr.constsResolve_mono htr, htb,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩, _, rfl, ?_⟩
    show env.find? cvA.name = none
    rw [hcvA]
    exact hfresh

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:232 foldIndMemberS_run
(its `EnvWF` half, pure) — **the member fold leaves a well-formed
environment**: `checkIndMember_wf` at each step, the block's pins carried
over each fresh cons by `EtaPins.step`. -/
theorem foldIndMember_envWF {μ : CheckMode} {F : Nat} {bn : List ConLeche.Name}
    {caps : IndCaps} :
    ∀ {cis : List ConstantInfo} {env e : Env}, EnvWF env →
      (∀ ci ∈ cis, ∀ cv caps₀, ci = .indInfo cv caps₀ →
        ConLeche.EtaPins μ env cv.name cv.levelParams caps) →
      cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ F) bn caps) env = .ok e →
      EnvWF e
  | [], env, e, henv, _, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact henv
  | ci :: cis, env, e, henv, hpins, h => by
    rw [List.foldlM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    · rename_i e₁ h₁
      obtain ⟨henv₁, c, rfl, hfresh⟩ := checkIndMember_wf henv (hpins ci List.mem_cons_self) h₁
      exact foldIndMember_envWF henv₁
        (fun x hx cv c0 hceq => (hpins x (List.mem_cons_of_mem _ hx) cv c0 hceq).step hfresh) h

theorem foldIndMember_up {μ : CheckMode} {F G : Nat} {bn : List ConLeche.Name}
    {caps : IndCaps} {cis : List ConstantInfo} {env e : Env} (hle : F ≤ G)
    (h : cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ F) bn caps) env = .ok e) :
    cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ G) bn caps) env = .ok e := by
  have e1 : ∀ F, cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ F) bn caps) env
      = (cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOpsM μ) bn caps) env).val F := by
    intro F
    rw [ConLeche.foldlM_atF]
    simp only [ConLeche.checkIndMember_datF]
  rw [e1] at h ⊢
  exact (cis.foldlM (ConLeche.checkIndMember (ConLeche.fueledOpsM μ) bn caps) env).property hle h

theorem checkIndRecs_up {μ : CheckMode} {F G : Nat} {bn : List ConLeche.Name}
    {env₂ e : Env} {recs : List ConstantInfo} (hle : F ≤ G)
    (h : ConLeche.checkIndRecs μ (ConLeche.fueledOps μ F) bn env₂ recs = .ok e) :
    ConLeche.checkIndRecs μ (ConLeche.fueledOps μ G) bn env₂ recs = .ok e := by
  rw [← ConLeche.checkIndRecs_datF] at h ⊢
  exact (ConLeche.checkIndRecs μ (ConLeche.fueledOpsM μ) bn env₂ recs).property hle h

theorem foldProjFn_up {μ : CheckMode} {F G : Nat} {T C : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nF : Nat} {xs : List Nat} {env e : Env} (hle : F ≤ G)
    (h : xs.foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOps μ F) T C lps nP nF) env
      = .ok e) :
    xs.foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOps μ G) T C lps nP nF) env
      = .ok e := by
  have e1 : ∀ F, xs.foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOps μ F) T C lps nP nF)
      env = (xs.foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOpsM μ) T C lps nP nF)
        env).val F := by
    intro F
    rw [ConLeche.foldlM_atF]
    simp only [ConLeche.installProjFnStep_datF]
  rw [e1] at h ⊢
  exact (xs.foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOpsM μ) T C lps nP nF)
    env).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:493 checkIndMember_datF. -/
theorem checkIndMember_up {μ : CheckMode} {F G : Nat} {bn : List ConLeche.Name}
    {caps : IndCaps} {env e : Env} {ci : ConstantInfo} (hle : F ≤ G)
    (h : ConLeche.checkIndMember (ConLeche.fueledOps μ F) bn caps env ci = .ok e) :
    ConLeche.checkIndMember (ConLeche.fueledOps μ G) bn caps env ci = .ok e := by
  rw [← ConLeche.checkIndMember_datF] at h ⊢
  exact (ConLeche.checkIndMember (ConLeche.fueledOpsM μ) bn caps env ci).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
(its shape) — **an accepted member step pushes one constant, which is not a
projection table.**  Structural. -/
theorem checkIndMember_push {μ : CheckMode} {bn : List NIdx} {caps : IIndCaps}
    {fe : IFEnv} {ci : IConstantInfo} {s s' : AState} {r : IFEnv}
    (h : Arena.checkIndMember μ bn caps fe ci s = .ok (r, s')) :
    ∃ ci', r = fe.push ci' ∧ ∀ t, ci' ≠ .projInfo t := by
  simp only [Arena.checkIndMember] at h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨cvA, _, _, h⟩ := bindOk h
  cases ci with
  | indInfo v c =>
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨_, rfl, fun t h => IConstantInfo.noConfusion h⟩
  | ctorInfo v a b =>
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨_, rfl, fun t h => IConstantInfo.noConfusion h⟩
  | axiomInfo v => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | defnInfo v e hint => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | thmInfo v e => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | recInfo v a b c => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | projInfo t => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
One member checked and installed at its real inductive kind.

`sorry`: `checkMemberVal_spec` and `IFEnv.push`'s two lemmas. -/
theorem checkIndMember_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (hcoh : IFEnvCoh fe') (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (caps : IIndCaps) (capsP : IndCaps)
    (ci : IConstantInfo) (ciP : ConstantInfo) :
    ISpec
      (fun s => ReadOK env fe' s ∧
        Frontend.denoteNList s.store.ns blockNames = some blockNamesP ∧
        Frontend.denoteCaps s.store caps = some capsP ∧
        Frontend.denoteCI s.store ci = some ciP ∧ denoteFEnv s.store fe' = some env)
      (Arena.checkIndMember μ blockNames caps fe' ci)
      (fun s r => CheckOK μ env fe' s ∧
        InstRel fe' (fun e => ∃ F, ConLeche.checkIndMember
          (ConLeche.fueledOps μ F) blockNamesP capsP env ciP = .ok e) s.store r) := by
  intro s₀ s' r hpre hrun
  obtain ⟨hread, hbn, hcaps, hci, hfe⟩ := hpre
  simp only [Arena.checkIndMember] at hrun
  -- the flush, at this member's index
  obtain ⟨u, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨hck₁, hi₁, hst₁⟩ := hread.flush (μ := μ) k1
  have hx₁ : Ext s₀.store s₁.store := hi₁.ext
  obtain ⟨cv, s₂, k2, z2⟩ := bindOk z1
  -- only a former or a constructor gets past the twin's last match
  have hkind : (∃ v c, ci = .indInfo v c) ∨ (∃ v a b, ci = .ctorInfo v a b) := by
    obtain ⟨cvA, _, _, h⟩ := bindOk z2
    cases ci with
    | indInfo v c => exact Or.inl ⟨v, c, rfl⟩
    | ctorInfo v a b => exact Or.inr ⟨v, a, b, rfl⟩
    | axiomInfo v => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | defnInfo v e hint => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | thmInfo v e => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | recInfo v a b c => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | projInfo t => exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  rcases hkind with ⟨v, c, rfl⟩ | ⟨v, a, b, rfl⟩
  · obtain ⟨vP, cP, rfl, hv, hc⟩ := denoteCI_ind_inv hci
    obtain ⟨rfl, rfl⟩ := pureOk k2
    obtain ⟨cvA, s₃, k3, z3⟩ := bindOk z2
    obtain ⟨c3, F, cvAP, hF, hcvA⟩ := checkMemberVal_spec fe' env hμ hk henv blockNames
      blockNamesP cv vP s₂ s₃ cvA hck₁
      ⟨denoteNListE_ext hx₁ _ _ hbn, denoteCV_ext hv hx₁, denoteFEnv_ext hx₁ hfe,
        denoteFEnv_ext hx₁ hfe⟩ k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    have hx₃ : Ext s₀.store s'.store := hx₁.trans c3.ext
    have hdci : Frontend.denoteCI s'.store (.indInfo cvA caps) = some (.indInfo cvAP capsP) := by
      simp only [Frontend.denoteCI, hcvA, denoteCaps_ext hcaps hx₃]
    refine ⟨hi₁.trans c3.toInst, c3.ok, hcoh.push _, Pushed.push _ _, Nat.le_succ _,
      ⟨_, denoteFEnv_push (denoteFEnv_ext hx₃ hfe) hdci, F, ?_⟩,
      ProjOut.push hcoh _ (fun t h => IConstantInfo.noConfusion h)⟩
    simp only [ConLeche.checkIndMember, bind, Except.bind, hF, pure, Except.pure,
      ConstantInfo.toConstantVal]
  · obtain ⟨vP, rfl, hv⟩ := denoteCI_ctor_inv hci
    obtain ⟨rfl, rfl⟩ := pureOk k2
    obtain ⟨cvA, s₃, k3, z3⟩ := bindOk z2
    obtain ⟨c3, F, cvAP, hF, hcvA⟩ := checkMemberVal_spec fe' env hμ hk henv blockNames
      blockNamesP cv vP s₂ s₃ cvA hck₁
      ⟨denoteNListE_ext hx₁ _ _ hbn, denoteCV_ext hv hx₁, denoteFEnv_ext hx₁ hfe,
        denoteFEnv_ext hx₁ hfe⟩ k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    have hx₃ : Ext s₀.store s'.store := hx₁.trans c3.ext
    have hdci : Frontend.denoteCI s'.store (.ctorInfo cvA a b) = some (.ctorInfo cvAP a b) := by
      simp only [Frontend.denoteCI, hcvA, Option.map_some]
    refine ⟨hi₁.trans c3.toInst, c3.ok, hcoh.push _, Pushed.push _ _, Nat.le_succ _,
      ⟨_, denoteFEnv_push (denoteFEnv_ext hx₃ hfe) hdci, F, ?_⟩,
      ProjOut.push hcoh _ (fun t h => IConstantInfo.noConfusion h)⟩
    simp only [ConLeche.checkIndMember, bind, Except.bind, hF, pure, Except.pure,
      ConstantInfo.toConstantVal]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
`checkIndMembers` is task #97d-2's explicit recursion for con-leche's
`foldlM` over the non-recursor members (deviation 3's fifth item).

`sorry`: a list induction over `checkIndMember_spec` and `InstRel.trans`
(closed, `Bridge/Inductives/Rel.lean`). -/
theorem checkIndMembers_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (hcoh : IFEnvCoh fe) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (caps : IIndCaps) (capsP : IndCaps)
    (cis : List IConstantInfo) (cisP : List ConstantInfo)
    (hpins : ∀ ci ∈ cisP, ∀ cv caps₀, ci = .indInfo cv caps₀ →
      ConLeche.EtaPins μ env cv.name cv.levelParams capsP) :
    ISpec
      (fun s => ReadOK env fe s ∧
        Frontend.denoteNList s.store.ns blockNames = some blockNamesP ∧
        Frontend.denoteCaps s.store caps = some capsP ∧
        Frontend.denoteCIList s.store cis = some cisP ∧ denoteFEnv s.store fe = some env)
      (Arena.checkIndMembers μ blockNames caps fe cis)
      (fun s r => InstRel fe (fun e => (∃ F,
        cisP.foldlM (ConLeche.checkIndMember (ConLeche.fueledOps μ F)
          blockNamesP capsP) env = .ok e) ∧ ReadOK e r s) s.store r) := by
  induction cis generalizing fe env cisP with
  | nil =>
    intro s₀ s' r hpre hrun
    obtain ⟨hread, hbn, hcaps, hcis, hfe⟩ := hpre
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcis
    subst hcis
    simp only [Arena.checkIndMembers] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨InstStep.refl hread.state, hcoh, Pushed.refl _, Nat.le_refl _,
      ⟨env, hfe, ⟨0, rfl⟩, hread⟩, ProjOut.refl _ _⟩
  | cons ci rest ih =>
    intro s₀ s' r hpre hrun
    obtain ⟨hread, hbn, hcaps, hcis, hfe⟩ := hpre
    simp only [Frontend.denoteCIList] at hcis
    cases hc : Frontend.denoteCI s₀.store ci with
    | none => rw [hc] at hcis; simp at hcis
    | some ciP =>
    cases hr : Frontend.denoteCIList s₀.store rest with
    | none => rw [hc, hr] at hcis; simp at hcis
    | some restP =>
    rw [hc, hr] at hcis
    obtain rfl := (Option.some.inj hcis).symm
    simp only [Arena.checkIndMembers] at hrun
    obtain ⟨fe₁, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨i1, hck₁, hinst₁⟩ := checkIndMember_spec fe hμ hk henv hcoh blockNames
      blockNamesP caps capsP ci ciP s₀ s₁ fe₁ ⟨hread, hbn, hcaps, hc, hfe⟩ k1
    obtain ⟨env₁, hden₁, F₁, hF₁⟩ := hinst₁.denote
    obtain ⟨henv₁, c₁, rfl, hfresh⟩ := checkIndMember_wf henv
      (hpins ciP List.mem_cons_self) hF₁
    obtain ⟨ci', hpush, hnp⟩ := checkIndMember_push k1
    have hx₁ := i1.ext
    have hread₁ : ReadOK ⟨c₁ :: env.consts⟩ fe₁ s₁ := by
      rw [hpush] at hden₁ ⊢
      exact hck₁.toR.push hcoh hnp (denoteFEnv_ext hx₁ hfe) hden₁
    obtain ⟨i2, hinst₂⟩ := ih (fe := fe₁) (env := ⟨c₁ :: env.consts⟩) (cisP := restP) henv₁
      hinst₁.coh
      (fun x hx cv c0 hceq => (hpins x (List.mem_cons_of_mem _ hx) cv c0 hceq).step hfresh)
      s₁ s' r ⟨hread₁, denoteNListE_ext hx₁ _ _ hbn, denoteCaps_ext hcaps hx₁,
        denoteCIList_ext hx₁ _ _ hr, hden₁⟩ z1
    refine ⟨i1.trans i2, (InstRel.trans i2.ext hinst₁ hinst₂).imp ?_⟩
    rintro e ⟨⟨F₂, hF₂⟩, hre⟩
    refine ⟨⟨max F₁ F₂, ?_⟩, hre⟩
    have g₁ := checkIndMember_up (Nat.le_max_left F₁ F₂) hF₁
    have g₂ := foldIndMember_up (Nat.le_max_right F₁ F₂) hF₂
    rw [List.foldlM_cons]
    simp only [bind, Except.bind, g₁]
    exact g₂

/-! ## The recursors -/

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
(its answer's second component) — a provisioned recursor list denotes: each
checked header, its major index, its rule prefix and its stream rules. -/
def denoteRecs (st : EStore) :
    List (IConstantVal × Nat × Nat × List IRecRule) →
      Option (List (ConstantVal × Nat × Nat × List RecRule))
  | [] => some []
  | (cv, mI, rP, rs) :: rest =>
    match Frontend.denoteCV st cv, Frontend.denoteRules st rs, denoteRecs st rest with
    | some cvP, some rsP, some restP => some ((cvP, mI, rP, rsP) :: restP)
    | _, _, _ => none


/-- con-leche: none — a provisioned recursor list keeps its denotation as
the arena grows. -/
theorem denoteRecs_ext {st st' : EStore} (hx : Ext st st') :
    ∀ {cs : List (IConstantVal × Nat × Nat × List IRecRule)}
      {csP : List (ConstantVal × Nat × Nat × List RecRule)},
      denoteRecs st cs = some csP → denoteRecs st' cs = some csP
  | [], csP, h => h
  | (cv, mI, rP, rs) :: rest, csP, h => by
    simp only [denoteRecs] at h ⊢
    split at h
    · rename_i a b c ha hb hc
      rw [denoteCV_ext ha hx, denoteRules_ext hx _ _ hb, denoteRecs_ext hx hc]
      exact h
    · exact nomatch h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:428 checkIotaRules_datF — one fuel
for the recursor group's install fold. -/
theorem iotaFold_up {μ : CheckMode} {F G : Nat} {env₂ envSelf : Env}
    {fP : ConLeche.Name → ConLeche.Name}
    {cs : List (ConstantVal × Nat × Nat × List RecRule)} {a e : Env} (hle : F ≤ G)
    (h : cs.foldlM (fun (a : Env) c => do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOps μ F) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env)) a = .ok e) :
    cs.foldlM (fun (a : Env) c => do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOps μ G) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env)) a = .ok e := by
  have e1 : ∀ F, cs.foldlM (fun (a : Env) c => do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOps μ F) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env)) a =
      (cs.foldlM (fun (a : Env) c => (do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOpsM μ) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env) :
            ConLeche.FueledM Env)) a).val F := by
    intro F
    rw [ConLeche.foldlM_atF]
    simp only [ConLeche.FueledM.atF_bind, ConLeche.checkIotaRules_datF,
      ConLeche.FueledM.atF_pure]
  rw [e1] at h ⊢
  exact (cs.foldlM (fun (a : Env) c => (do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOpsM μ) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env) :
            ConLeche.FueledM Env)) a).property hle h

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:140 envWF_cons_provRec — **a
provisioned (rule-less) recursor keeps the environment well formed**: its
header is `checkMemberVal`'s checked constant, closed and resolving, and fresh;
a rule-less record has no rule clause to owe. -/
theorem provRec_envWF {μ : CheckMode} {F : Nat} {bn : List ConLeche.Name} {env : Env}
    {cv cvA : ConstantVal} {mI rP : Nat} (henv : EnvWF env)
    (h : ConLeche.checkMemberVal (ConLeche.fueledOps μ F) bn env cv = .ok cvA) :
    EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ ∧ env.find? cvA.name = none := by
  obtain ⟨hccv, -⟩ := ConLeche.checkMemberVal_inv h
  obtain ⟨htf, htp, htr, htb⟩ := ConLeche.checkConstantVal_typeWF hccv
  obtain ⟨hfresh, -, -, -, -, -, type, -, -, -, -, -, -, -, hcvA⟩ :=
    ConLeche.checkConstantVal_inv hccv
  refine ⟨ConLeche.EnvWF.cons henv ⟨htf, htp, Expr.constsResolve_mono htr, htb,
    (fun _ _ _ heq => nomatch heq), ?_, (fun _ heq => nomatch heq),
    (fun _ _ heq => nomatch heq)⟩, by rw [hcvA]; exact hfresh⟩
  intro cv' mI' rP' rules heq r hr
  injection heq with _ _ _ h4
  subst h4
  exact nomatch hr

theorem checkMemberVal_up {μ : CheckMode} {F G : Nat} {bn : List ConLeche.Name} {env : Env}
    {cv cvA : ConstantVal} (hle : F ≤ G)
    (h : ConLeche.checkMemberVal (ConLeche.fueledOps μ F) bn env cv = .ok cvA) :
    ConLeche.checkMemberVal (ConLeche.fueledOps μ G) bn env cv = .ok cvA := by
  rw [← ConLeche.checkMemberVal_datF] at h ⊢
  exact (ConLeche.checkMemberVal (ConLeche.fueledOpsM μ) bn env cv).property hle h

theorem provisionRecs_up {μ : CheckMode} {F G : Nat} {bn : List ConLeche.Name} {env : Env}
    {cis : List ConstantInfo} {v : Env × List (ConstantVal × Nat × Nat × List RecRule)}
    (hle : F ≤ G)
    (h : ConLeche.provisionRecs (ConLeche.fueledOps μ F) bn env cis = .ok v) :
    ConLeche.provisionRecs (ConLeche.fueledOps μ G) bn env cis = .ok v := by
  rw [← ConLeche.provisionRecs_datF] at h ⊢
  exact (ConLeche.provisionRecs (ConLeche.fueledOpsM μ) bn env cis).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
The recursors' headers checked and PROVISIONALLY installed (their rules may
mention each other, so they install as a group).

`sorry`: `checkMemberVal_spec` and `IFEnv.push`, over a list induction. -/
theorem provisionRecs_spec {μ : CheckMode} {env : Env} (feAcc : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (hcoh : IFEnvCoh feAcc) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (cis : List IConstantInfo)
    (cisP : List ConstantInfo) :
    ISpec
      (fun s => ReadOK env feAcc s ∧
        Frontend.denoteNList s.store.ns blockNames = some blockNamesP ∧
        Frontend.denoteCIList s.store cis = some cisP ∧
        denoteFEnv s.store feAcc = some env)
      (Arena.provisionRecs μ blockNames feAcc cis)
      (fun s r => ∃ F envP recsP,
        ConLeche.provisionRecs (ConLeche.fueledOps μ F) blockNamesP env cisP
          = .ok (envP, recsP) ∧
        InstRel feAcc (fun e => e = envP) s.store r.1 ∧
        denoteRecs s.store r.2 = some recsP ∧ ReadOK envP r.1 s) := by
  induction cis generalizing feAcc env cisP with
  | nil =>
    intro s₀ s' r hpre hrun
    obtain ⟨hread, hbn, hcis, hfe⟩ := hpre
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcis
    subst hcis
    simp only [Arena.provisionRecs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨InstStep.refl hread.state, 0, env, [], rfl,
      ⟨hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, rfl⟩, ProjOut.refl _ _⟩, rfl, hread⟩
  | cons ci rest ih =>
    intro s₀ s' r hpre hrun
    obtain ⟨hread, hbn, hcis, hfe⟩ := hpre
    simp only [Frontend.denoteCIList] at hcis
    cases hc : Frontend.denoteCI s₀.store ci with
    | none => rw [hc] at hcis; simp at hcis
    | some ciP =>
    cases hr : Frontend.denoteCIList s₀.store rest with
    | none => rw [hc, hr] at hcis; simp at hcis
    | some restP =>
    rw [hc, hr] at hcis
    obtain rfl := (Option.some.inj hcis).symm
    simp only [Arena.provisionRecs] at hrun
    cases ci
    case recInfo v mI rP rules =>
      obtain ⟨vP, rulesP, rfl, hv, hrules⟩ := denoteCI_rec_inv hc
      obtain ⟨u, s₁, k1, z1⟩ := bindOk hrun
      obtain ⟨hck₁, hi₁, hst₁⟩ := hread.flush (μ := μ) k1
      have hx₁ : Ext s₀.store s₁.store := hi₁.ext
      obtain ⟨cv, s₂, k2, z2⟩ := bindOk z1
      obtain ⟨hcv, hs₂⟩ := pureOk k2
      subst hcv
      rw [hs₂] at z2
      obtain ⟨cvA, s₃, k3, z3⟩ := bindOk z2
      obtain ⟨c3, F₁, cvAP, hF₁, hcvA⟩ := checkMemberVal_spec feAcc env hμ hk henv blockNames
        blockNamesP cv vP s₁ s₃ cvA hck₁
        ⟨denoteNListE_ext hx₁ _ _ hbn, denoteCV_ext hv hx₁, denoteFEnv_ext hx₁ hfe,
          denoteFEnv_ext hx₁ hfe⟩ k3
      obtain ⟨henv₁, hfresh⟩ := provRec_envWF (mI := mI) (rP := rP) henv hF₁
      have hx₃ : Ext s₀.store s₃.store := hx₁.trans c3.ext
      have hci : Frontend.denoteCI s₃.store (.recInfo cvA mI rP []) =
          some (.recInfo cvAP mI rP []) := by
        simp only [Frontend.denoteCI, hcvA, Frontend.denoteRules]
      have hpush := denoteFEnv_push (denoteFEnv_ext hx₃ hfe) hci
      have hread₃ := c3.ok.toR.push hcoh (fun t h => IConstantInfo.noConfusion h)
        (denoteFEnv_ext hx₃ hfe) hpush
      obtain ⟨t, s₄, k4, z4⟩ := bindOk z3
      obtain ⟨i4, F₂, envP, recsP, hF₂, hinst, hrecs, hreadP⟩ :=
        ih (feAcc := feAcc.push (.recInfo cvA mI rP [])) (env := ⟨.recInfo cvAP mI rP [] ::
          env.consts⟩) (cisP := restP) henv₁ (hcoh.push _) s₃ s₄ t
          ⟨hread₃, denoteNListE_ext hx₃ _ _ hbn, denoteCIList_ext hx₃ _ _ hr, hpush⟩ k4
      obtain ⟨rfl, rfl⟩ := pureOk z4
      have x4 := i4.ext
      refine ⟨hi₁.trans (c3.toInst.trans i4), max F₁ F₂, envP,
        (cvAP, mI, rP, rulesP) :: recsP, ?_, ?_, ?_, hreadP⟩
      · have g₁ := checkMemberVal_up (Nat.le_max_left F₁ F₂) hF₁
        have g₂ := provisionRecs_up (Nat.le_max_right F₁ F₂) hF₂
        simp only [ConLeche.provisionRecs, ConstantInfo.toConstantVal, bind, Except.bind, g₁, g₂,
          pure, Except.pure]
      · have h1 : InstRel feAcc (fun _ => True) s₃.store (feAcc.push (.recInfo cvA mI rP [])) :=
          ⟨hcoh.push _, Pushed.push _ _, Nat.le_succ _, ⟨_, hpush, trivial⟩,
            ProjOut.push hcoh _ (fun t h => IConstantInfo.noConfusion h)⟩
        exact InstRel.trans x4 h1 hinst
      · simp only [denoteRecs, denoteCV_ext hcvA x4,
          denoteRules_ext (hx₃.trans x4) _ _ hrules, hrecs]
    all_goals exact absurd hrun (fun h => failOk h)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
`installIndRecs` is the twin's explicit recursion for con-leche's inner fold:
each provisioned recursor's rules certified and the record installed.

`sorry`: `checkIotaRules_spec` and `IFEnv.push`, over a list induction. -/
theorem installIndRecs_spec {μ : CheckMode} (fe₂ feSelf acc : IFEnv)
    (env₂ envSelf envAcc : Env) (hk : CoreSpec μ Arena.checkFuel)
    (henvSelf : EnvWF envSelf) (hcoh : IFEnvCoh acc)
    (tbl : List (NIdx × NIdx)) (fP : ConLeche.Name → ConLeche.Name)
    (cs : List (IConstantVal × Nat × Nat × List IRecRule))
    (csP : List (ConstantVal × Nat × Nat × List RecRule)) :
    CSpec μ envSelf feSelf
      (fun st => RenameRelW st tbl fP ∧ denoteFEnv st fe₂ = some env₂ ∧
        denoteFEnv st feSelf = some envSelf ∧
        denoteFEnv st acc = some envAcc ∧ IFEnvOKS env₂ fe₂ st ∧
        denoteRecs st cs = some csP ∧ IFEnvOKS envAcc acc st)
      (Arena.installIndRecs μ fe₂ feSelf tbl acc cs)
      (fun st r => InstRel acc (fun e => (∃ F, csP.foldlM (fun (a : Env) c => do
          let rules' ← ConLeche.checkIotaRules μ (ConLeche.fueledOps μ F) env₂ envSelf fP
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: a.consts⟩ : Env)) envAcc
        = .ok e) ∧ IFEnvOKS e r st) st r) := by
  induction cs generalizing acc envAcc csP with
  | nil =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨-, -, -, hacc, -, hcs, hokA⟩ := hpre
    simp only [denoteRecs, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.installIndRecs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hck, hcoh, Pushed.refl _, Nat.le_refl _,
      ⟨envAcc, hacc, ⟨0, rfl⟩, hokA⟩, ProjOut.refl _ _⟩
  | cons c cs ih =>
    intro s₀ s' r hck hpre hrun
    obtain ⟨hren, hfe₂, hfeS, hacc, hok₂, hcs, hokA⟩ := hpre
    obtain ⟨cv, mI, rP, rs⟩ := c
    simp only [denoteRecs] at hcs
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cvP =>
    cases hrs : Frontend.denoteRules s₀.store rs with
    | none => rw [hcv, hrs] at hcs; simp at hcs
    | some rsP =>
    cases hrest : denoteRecs s₀.store cs with
    | none => rw [hcv, hrs, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrs, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    simp only [Arena.installIndRecs] at hrun
    obtain ⟨rules', s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, F₁, rlsP, hF₁, hrls⟩ := checkIotaRules_spec fe₂ feSelf env₂ envSelf hk henvSelf
      tbl fP cv.name cvP.name cv.levelParams cvP.levelParams cv.type cvP.type mI rP 0 rs rsP
      s₀ s₁ rules' hck ⟨hren, denoteCV_name hcv, denoteCV_lps hcv, denoteCV_type hcv, hrs,
        hfe₂, hfeS, hok₂⟩ k1
    have x1 := c1.ext
    have hci : Frontend.denoteCI s₁.store (.recInfo cv mI rP rules') =
        some (.recInfo cvP mI rP rlsP) := by
      simp only [Frontend.denoteCI, denoteCV_ext hcv x1, hrls]
    have hpush := denoteFEnv_push (denoteFEnv_ext x1 hacc) hci
    have hokA₁ : IFEnvOKS ⟨.recInfo cvP mI rP rlsP :: envAcc.consts⟩
        (acc.push (.recInfo cv mI rP rules')) s₁.store := by
      intro t ht
      have h0 : IFEnvOK envAcc acc t := hokA.mono x1 t ht
      obtain ⟨c, hc, he⟩ := denoteFEnv_push_inv (denoteFEnv_ext x1 hacc) hpush
      have hst : StateOK t := ⟨by rw [ht]; exact c1.ok.state.wf⟩
      have := h0.push hst hcoh (fun t' h => IConstantInfo.noConfusion h) (by rw [ht]; exact hci)
      exact this
    obtain ⟨c2, hinst₂⟩ := ih (acc.push (.recInfo cv mI rP rules'))
      ⟨.recInfo cvP mI rP rlsP :: envAcc.consts⟩ (hcoh.push _) restP s₁ s' r c1.ok
      ⟨hren.mono x1, denoteFEnv_ext x1 hfe₂, denoteFEnv_ext x1 hfeS, hpush, hok₂.mono x1,
        denoteRecs_ext x1 hrest, hokA₁⟩ z1
    refine ⟨c1.trans c2, ?_⟩
    have h1 : InstRel acc (fun _ => True) s₁.store (acc.push (.recInfo cv mI rP rules')) :=
      ⟨hcoh.push _, Pushed.push _ _, Nat.le_succ _, ⟨_, hpush, trivial⟩,
        ProjOut.push hcoh _ (fun t h => IConstantInfo.noConfusion h)⟩
    refine (InstRel.trans c2.ext h1 hinst₂).imp ?_
    rintro e ⟨⟨F₂, hF₂⟩, hr⟩
    refine ⟨⟨max F₁ F₂, ?_⟩, hr⟩
    have g₁ : ConLeche.checkIotaRules μ (ConLeche.fueledOps μ (max F₁ F₂)) env₂ envSelf fP
        cvP.name cvP.levelParams cvP.type mI rP 0 rsP = .ok rlsP := by
      rw [← ConLeche.checkIotaRules_datF] at hF₁ ⊢
      exact (ConLeche.checkIotaRules μ (ConLeche.fueledOpsM μ) env₂ envSelf fP cvP.name
        cvP.levelParams cvP.type mI rP 0 rsP).property (Nat.le_max_left F₁ F₂) hF₁
    have g₂ := iotaFold_up (μ := μ) (Nat.le_max_right F₁ F₂) hF₂
    rw [List.foldlM_cons]
    simp only [bind, Except.bind, g₁, pure, Except.pure]
    exact g₂

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:281 provisionRecsS_run (its
`EnvWF` half, pure) — **the provisioned environment is well formed**:
`provRec_envWF` at each rule-less cons. -/
theorem provisionRecs_envWF {μ : CheckMode} {F : Nat} {bn : List ConLeche.Name} :
    ∀ {cis : List ConstantInfo} {env : Env}
      {v : Env × List (ConstantVal × Nat × Nat × List RecRule)}, EnvWF env →
      ConLeche.provisionRecs (ConLeche.fueledOps μ F) bn env cis = .ok v → EnvWF v.1
  | [], env, v, henv, h => by
    simp only [ConLeche.provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact henv
  | ci :: rest, env, v, henv, h => by
    cases ci
    case recInfo cv mI rP rules =>
      simp only [ConLeche.provisionRecs, bind, Except.bind] at h
      split at h
      · exact nomatch h
      · rename_i cvA hcm
        split at h
        · exact nomatch h
        · rename_i w hw
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact provisionRecs_envWF (v := w) (provRec_envWF (mI := mI) (rP := rP) henv hcm).1 hw
    all_goals simp [ConLeche.provisionRecs, throw, throwThe, MonadExceptOf.throw] at h

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
The recursor group: the pinned `Eq` basis, the provisioning, the rename table
and the certified installs.

`sorry`: `eqBasisStored_spec`, `provisionRecs_spec`, `blockRenameTable_spec`
and `installIndRecs_spec`. -/
theorem checkIndRecs_spec {μ : CheckMode} {env : Env} (fe₂ : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (hcoh : IFEnvCoh fe₂) (blockNames : List NIdx)
    (blockNamesP : List ConLeche.Name) (recs : List IConstantInfo)
    (recsP : List ConstantInfo) :
    ISpec
      (fun s => ReadOK env fe₂ s ∧
        Frontend.denoteNList s.store.ns blockNames = some blockNamesP ∧
        Frontend.denoteCIList s.store recs = some recsP ∧
        denoteFEnv s.store fe₂ = some env)
      (Arena.checkIndRecs μ blockNames fe₂ recs)
      (fun s r => InstRel fe₂ (fun e => (∃ F, ConLeche.checkIndRecs
        μ (ConLeche.fueledOps μ F) blockNamesP env recsP = .ok e) ∧ ReadOK e r s)
        s.store r) := by
  intro s₀ s' r hpre hrun
  obtain ⟨hread, hbn, hrecs, hfe⟩ := hpre
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  have hlen : recs.length = recsP.length := by
    clear hrun
    induction recs generalizing recsP with
    | nil => simp only [Frontend.denoteCIList, Option.some.injEq] at hrecs; subst hrecs; rfl
    | cons x xs ih =>
      simp only [Frontend.denoteCIList] at hrecs
      split at hrecs
      · rename_i a b ha hb
        obtain rfl := (Option.some.inj hrecs).symm
        simp only [List.length_cons, ih _ hb]
      · exact nomatch hrecs
  simp only [Arena.checkIndRecs] at hrun
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    have hempP : recsP.isEmpty = true := by
      rw [List.isEmpty_iff] at hemp ⊢
      subst hemp
      exact List.length_eq_zero_iff.mp hlen.symm
    exact ⟨InstStep.refl hread.state, hcoh, Pushed.refl _, Nat.le_refl _,
      ⟨env, hfe, ⟨0, by simp only [ConLeche.checkIndRecs, if_pos hempP]; rfl⟩, hread⟩,
      ProjOut.refl _ _⟩
  rw [if_neg hemp] at hrun
  have hempP : ¬ recsP.isEmpty = true := by
    intro h
    rw [List.isEmpty_iff] at hemp h
    subst h
    exact hemp (List.length_eq_zero_iff.mp hlen)
  -- the rename table
  obtain ⟨tbl, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, htbl⟩ := blockRenameTable_specW blockNames blockNamesP s₀ s₁ tbl hread.state
    hbn k1
  -- the pinned `Eq`
  have hread₁ : ReadOK env fe₂ s₁ := hread.mono p1.ok p1.ext p1.pins
  obtain ⟨b2, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨i2, hb2⟩ := eqBasisStored_run fe₂ s₁ s₂ b2 hread₁ k2
  obtain ⟨hg, z3⟩ := AM.dunless_ok hnever z2
  replace z3 := AM.pure_bind_ok z3
  rw [hb2] at hg
  have heq : env.find? ConLeche.eqName = some ConLeche.eqA := by simpa using hg
  -- the provisioning
  have x02 : Ext s₀.store s₂.store := p1.ext.trans i2.ext
  obtain ⟨t3, s₃, k3, z4⟩ := bindOk z3
  obtain ⟨i3, F₁, envSelf, checkedP, hF₁, hinstS, hchecked, hreadS⟩ := provisionRecs_spec fe₂
    hμ hk henv hcoh blockNames blockNamesP recs recsP s₂ s₃ t3
    ⟨hread₁.ofInst i2, denoteNListE_ext x02 _ _ hbn, denoteCIList_ext x02 _ _ hrecs,
      denoteFEnv_ext x02 hfe⟩ k3
  obtain ⟨feSelf, checked⟩ := t3
  simp only at hinstS hchecked hreadS z4
  have henvS := provisionRecs_envWF (v := (envSelf, checkedP)) henv hF₁
  -- the flush, then the certified installs at the provisioned index
  obtain ⟨u4, s₄, k4, z5⟩ := bindOk z4
  obtain ⟨hck₄, hi₄, hst₄⟩ := hreadS.flush (μ := μ) k4
  have x14 : Ext s₁.store s₄.store := by rw [hst₄]; exact i2.ext.trans i3.ext
  have x04 : Ext s₀.store s₄.store := p1.ext.trans x14
  have hfe₄ := denoteFEnv_ext x04 hfe
  have hok₂ : IFEnvOKS env fe₂ s₄.store := (hread.ienv.toS).mono x04
  obtain ⟨c5, hinst⟩ := installIndRecs_spec fe₂ feSelf fe₂ env envSelf env hk henvS hcoh tbl
    (fun n => if blockNamesP.contains n then n.str "_model" else n) checked checkedP s₄ s' r
    hck₄ ⟨fun st' hx hwf => htbl st' (x14.trans hx) hwf, hfe₄,
      by obtain ⟨e, he, rfl⟩ := hinstS.denote; rw [hst₄]; exact he,
      hfe₄, hok₂, by rw [hst₄]; exact hchecked, hok₂⟩ z5
  refine ⟨p1.toInst.trans (i2.trans (i3.trans (hi₄.trans c5.toInst))), hinst.imp ?_⟩
  rintro e ⟨⟨F₂, hF₂⟩, hokE⟩
  refine ⟨⟨max F₁ F₂, ?_⟩, ⟨c5.ok.state, c5.ok.pins, hokE s' rfl⟩⟩
  have g₁ := provisionRecs_up (Nat.le_max_left F₁ F₂) hF₁
  have g₂ := iotaFold_up (μ := μ) (Nat.le_max_right F₁ F₂) hF₂
  simp only [ConLeche.checkIndRecs, if_neg hempP, heq, bind, Except.bind, g₁]
  exact g₂

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

**CLOSED** (task #97-P3-Ind round 7): `projBack_specW`/`projFwd_specW` (the
rename tables' relation at every well-formed extension: the twin builds BOTH
tables before it renames, so the back table is read at a store the forward
table's interns grew), `renameConstsFast_pstep` twice, `beq_ehandle_eq` for
the roundtrip, and the four scoping guards' run forms (the layout move's
`allLevelParamsDefined_run`/`constsResolveFFast_run`,
`looseBVarsBoundedFast_spec`, `hasFvarFast_spec`) and `stripPis_pstep`.
(The old note's list named the wrong function's pieces.) -/
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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hC, hlps, hm, hfe⟩ := hpre
  simp only [Arena.checkProjTy] at hrun
  obtain ⟨back, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hback⟩ := projBack_specW T ctorName TP ctorNameP nF s₀ s1 back hok.state
    ⟨hT, hC⟩ k1
  obtain ⟨fwd, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hfwd⟩ := projFwd_specW T ctorName TP ctorNameP nF s1 s2 fwd p1.ok
    ⟨denoteN_ext hT p1.ext, denoteN_ext hC p1.ext⟩ k2
  obtain ⟨pty, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, -, hpty⟩ := renameConstsFast_pstep p2.ok (hback s2.store p2.ext p2.ok.wf)
    (denote_ext hm (p1.ext.trans p2.ext)) k3
  obtain ⟨rt, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, -, hrt⟩ := renameConstsFast_pstep p3.ok
    (hfwd s3.store p3.ext p3.ok.wf) hpty k4
  have p04 : PStep s₀ s4 := p1.trans (p2.trans (p3.trans p4))
  have ck4 := (p04.toCore hok).ok
  have hwf4 := ck4.state.wf
  rw [beq_ehandle_eq hwf4 hrt (denote_ext hm p04.ext)] at z4
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  obtain ⟨h1, z5⟩ := AM.dunless_ok hnever z4
  replace z5 := AM.pure_bind_ok z5
  have hpty4 := denote_ext hpty p4.ext
  obtain ⟨b2, s5, k5, z6⟩ := bindOk z5
  obtain ⟨p5, hb2⟩ := constsResolveFFast_pstep ck4.toR hpty4 k5
  obtain ⟨h2, z7⟩ := AM.dunless_ok hnever z6
  replace z7 := AM.pure_bind_ok z7
  subst hb2
  have hpty5 := denote_ext hpty4 p5.ext
  obtain ⟨b3, s6, k6, z8⟩ := bindOk z7
  obtain ⟨h61, h62, h63, hb3⟩ := AM.of_run (P := fun t => t = s5) rfl k6
    (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s5 pty p5.ok
      (by rw [hpty5]; rfl))
  have p6 : PStep s5 s6 := PStep.of_caches ⟨by rw [h61]; exact p5.ok.wf⟩
    (by rw [h61]; exact Ext.refl _) (by rw [h61]; exact BMExt.refl _) h62 h63
  have hpty6 : denoteE s6.store pty =
      some (mtyP.renameConsts (ConLeche.projBack TP ctorNameP nF)) := by rw [h61]; exact hpty5
  obtain ⟨b4, s7, k7, z9⟩ := bindOk z8
  obtain ⟨h71, h72, h73, hb4⟩ := AM.of_run (P := fun t => t = s6) rfl k7
    (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s6 pty p6.ok (by rw [hpty6]; rfl))
  have p7 : PStep s6 s7 := PStep.of_caches ⟨by rw [h71]; exact p6.ok.wf⟩
    (by rw [h71]; exact Ext.refl _) (by rw [h71]; exact BMExt.refl _) h72 h73
  have hpty7 : denoteE s7.store pty =
      some (mtyP.renameConsts (ConLeche.projBack TP ctorNameP nF)) := by rw [h71]; exact hpty6
  obtain ⟨b5, s8, k8, z10⟩ := bindOk z9
  have x07 : Ext s₀.store s7.store := p04.ext.trans (p5.ext.trans (p6.ext.trans p7.ext))
  obtain ⟨h81, h82, h83, hb5⟩ := allLevelParamsDefined_run p7.ok
    (denoteNListE_ext x07 _ _ hlps) hpty7 k8
  have p8 : PStep s7 s8 := PStep.of_caches ⟨by rw [h81]; exact p7.ok.wf⟩
    (by rw [h81]; exact Ext.refl _) (by rw [h81]; exact BMExt.refl _) h82 h83
  have hb3' := hb3 _ hpty5
  have hb4' := hb4 _ hpty6
  subst hb3' hb4' hb5
  obtain ⟨h3, z11⟩ := AM.dunless_ok hnever z10
  replace z11 := AM.pure_bind_ok z11
  have hpty8 : denoteE s8.store pty =
      some (mtyP.renameConsts (ConLeche.projBack TP ctorNameP nF)) := by rw [h81]; exact hpty7
  obtain ⟨sq, s9, k9, z12⟩ := bindOk z11
  obtain ⟨hs9, hsq⟩ := stripPis_pstep p8.ok hpty8 k9
  rw [hs9] at z12
  obtain ⟨h4, z13⟩ := AM.dunless_ok hnever z12
  replace z13 := AM.pure_bind_ok z13
  obtain ⟨rfl, rfl⟩ := pureOk z13
  have hsome : (Expr.stripPis (nP + 1) (mtyP.renameConsts (ConLeche.projBack TP ctorNameP nF))).isSome
      = true := by
    rcases sq with _ | ⟨bs, e⟩
    · exact absurd h4 (by simp)
    · obtain ⟨xs, x, hx, -⟩ := stripPis_some hsq
      rw [hx]; rfl
  refine ⟨(p04.trans (p5.trans (p6.trans (p7.trans p8)))).toCore hok, _, ?_, hpty8⟩
  simp only [ConLeche.checkProjTy, bind, Except.bind, pure, Except.pure]
  rw [if_pos (by simpa using h1), if_pos h2, if_pos (by simpa using h3), if_pos hsome]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
The projection function's iota certificate.

`sorry`: `projBack_spec`/`projFwd_spec`, `domsMatchRenamed_spec`,
`eqApp3?_spec` and `CoreSpec.knot`'s `defeq` slot. -/
theorem checkProjIota_spec {μ : CheckMode} (fe' feSelf : IFEnv)
    (env' envSelf : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF envSelf)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (cvj : IConstantVal) (cvjP : ConstantVal)
    (nP nF i : Nat) :
    CSpec μ envSelf feSelf
      (fun st => denoteN st.ns T = some TP ∧
        denoteN st.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        Frontend.denoteCV st cvj = some cvjP ∧
        denoteFEnv st fe' = some env' ∧ denoteFEnv st feSelf = some envSelf ∧
        IFEnvOKS env' fe' st)
      (Arena.checkProjIota μ fe' feSelf T ctorName lps cvj nP nF i)
      (fun _ _ => ∃ F, ConLeche.checkProjIota μ (ConLeche.fueledOps μ F) env'
        envSelf TP ctorNameP lpsP cvjP nP nF i = .ok ()) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
One projection function checked and installed.

`sorry`: `checkProjLookups_spec`, `checkProjTy_spec`, `checkProjIota_spec`,
`CoreSpec.knot`'s `defeq` slot and `IFEnv.push`. -/
theorem checkProjFn_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (hcoh : IFEnvCoh fe')
    (T ctorName : NIdx)
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

/-- con-leche: none — the constructor tag of a stored constant, on each side. -/
def iciKind : IConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo .. => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5 | .projInfo .. => 6

/-- con-leche: none — the same on con-leche's side. -/
def ciKind : ConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo .. => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5 | .projInfo .. => 6

/-- con-leche: none — **`Frontend.denoteCI` keeps the constructor**: the
fallthrough arm of a `match` on a stored constant's kind is the same arm on
both sides. -/
theorem denoteCI_kind {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) : iciKind ci = ciKind c := by
  cases ci
  case axiomInfo v => obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv h; rfl
  case defnInfo v _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv h; rfl
  case thmInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv h; rfl
  case indInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv h; rfl
  case ctorInfo v _ _ => obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv h; rfl
  case recInfo v _ _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv h; rfl
  case projInfo t => obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv h; rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux — **the
arena's binder comparison IS con-leche's at `g := fun _ e => e`**: the handle
arrays are the lists' `toArray`, and each handle comparison is
`beq_ehandle_eq`. -/
theorem domsMatchAux_eq {st : EStore} (hwf : StoreWF st)
    {bs₁ bs₂ : List (EIdx × BinderMeta)} {xs₁ xs₂ : List (Expr × BinderMeta)}
    (h1 : denoteBinders st bs₁ = some xs₁) (h2 : denoteBinders st bs₂ = some xs₂)
    (o₁ o₂ : Nat) : ∀ n, Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ n =
      ConLeche.domsMatchAux (fun _ e => e) xs₁ xs₂ o₁ o₂ n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [domsMatchAux_succ]
    have hA : Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ (k + 1) =
        (Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ k &&
          (match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
           | some b₁, some b₂ => b₁.1 == b₂.1
           | _, _ => false)) := by
      simp only [Arena.domsMatchAux, List.range_succ, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, List.getElem?_toArray]
      rfl
    rw [hA, ih]
    congr 1
    obtain ⟨hA1, hB1⟩ := denoteBinders_getElem? h1 (o₁ + k)
    obtain ⟨hA2, hB2⟩ := denoteBinders_getElem? h2 (o₂ + k)
    cases hb1 : bs₁[o₁ + k]? with
    | none => simp [hB1 hb1]
    | some p1 =>
    obtain ⟨t1, m1⟩ := p1
    obtain ⟨t1P, hp1, hd1⟩ := hA1 t1 m1 hb1
    cases hb2 : bs₂[o₂ + k]? with
    | none => simp [hp1, hB2 hb2]
    | some p2 =>
    obtain ⟨t2, m2⟩ := p2
    obtain ⟨t2P, hp2, hd2⟩ := hA2 t2 m2 hb2
    simp only [hp1, hp2]
    exact beq_ehandle_eq hwf hd1 hd2

/-- con-leche: none — **a stored theorem, read back through the index**:
`IFEnvOK`'s `cover` at a theorem, with the handle it is stored under pinned by
`denoteN_inj`. -/
theorem IFEnvOK.find_thm {env : Env} {fe : IFEnv} {s : AState} (hok : StateOK s)
    (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) {cvP : ConstantVal} {xP : Expr}
    (he : env.find? nm = some (.thmInfo cvP xP)) :
    ∃ cv x, fe.find? n = some (.thmInfo cv x) ∧
      Frontend.denoteCV s.store cv = some cvP ∧ denoteE s.store x = some xP := by
  obtain ⟨n', ci, hn', hf, hci⟩ := h.cover _ _ he
  have hwf := hok.wf
  obtain ⟨rk, hrk⟩ := hwf
  obtain rfl := denoteN_inj hrk.nsWF hn' hd
  cases ci
  case thmInfo v x =>
    obtain ⟨cv', x', he', hv, hx⟩ := denoteCI_thm_inv hci
    simp only [ConstantInfo.thmInfo.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exact ⟨v, x, hf, hv, hx⟩
  case axiomInfo v => obtain ⟨_, he', _⟩ := denoteCI_axiom_inv hci; cases he'
  case ctorInfo v _ _ => obtain ⟨_, he', _⟩ := denoteCI_ctor_inv hci; cases he'
  case defnInfo v _ _ => obtain ⟨_, _, he', _⟩ := denoteCI_defn_inv hci; cases he'
  case indInfo v _ => obtain ⟨_, _, he', _⟩ := denoteCI_ind_inv hci; cases he'
  case recInfo v _ _ _ => obtain ⟨_, _, he', _⟩ := denoteCI_rec_inv hci; cases he'
  case projInfo t => obtain ⟨_, he', _⟩ := denoteCI_proj_inv hci; cases he'

/-- con-leche: none — the same at a stored definition. -/
theorem IFEnvOK.find_defn {env : Env} {fe : IFEnv} {s : AState} (hok : StateOK s)
    (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) {cvP : ConstantVal} {xP : Expr}
    {hint : ReducibilityHint}
    (he : env.find? nm = some (.defnInfo cvP xP hint)) :
    ∃ cv x, fe.find? n = some (.defnInfo cv x hint) ∧
      Frontend.denoteCV s.store cv = some cvP ∧ denoteE s.store x = some xP := by
  obtain ⟨n', ci, hn', hf, hci⟩ := h.cover _ _ he
  have hwf := hok.wf
  obtain ⟨rk, hrk⟩ := hwf
  obtain rfl := denoteN_inj hrk.nsWF hn' hd
  cases ci
  case defnInfo v x h =>
    obtain ⟨cv', x', he', hv, hx⟩ := denoteCI_defn_inv hci
    simp only [ConstantInfo.defnInfo.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    exact ⟨v, x, hf, hv, hx⟩
  case axiomInfo v => obtain ⟨_, he', _⟩ := denoteCI_axiom_inv hci; cases he'
  case ctorInfo v _ _ => obtain ⟨_, he', _⟩ := denoteCI_ctor_inv hci; cases he'
  case thmInfo v _ => obtain ⟨_, _, he', _⟩ := denoteCI_thm_inv hci; cases he'
  case indInfo v _ => obtain ⟨_, _, he', _⟩ := denoteCI_ind_inv hci; cases he'
  case recInfo v _ _ _ => obtain ⟨_, _, he', _⟩ := denoteCI_rec_inv hci; cases he'
  case projInfo t => obtain ⟨_, he', _⟩ := denoteCI_proj_inv hci; cases he'

/-- con-leche: none — **`List.allM` of a core-grade step**: `allM_pstep` at
the `CheckOK` frame, for a body that reads the index. -/
theorem allM_cstep {μ : CheckMode} {env : Env} {fe : IFEnv} {α : Type}
    {f : α → AM Bool} {g : α → Bool} (P : α → EStore → Prop)
    (hPx : ∀ {a : α} {st st' : EStore}, Ext st st' → P a st → P a st')
    (hf : ∀ (a : α) (s₀ s' : AState) (b : Bool), CheckOK μ env fe s₀ → P a s₀.store →
      f a s₀ = .ok (b, s') → CoreStep μ env fe s₀ s' ∧ b = g a) :
    ∀ (xs : List α) (s₀ s' : AState) (b : Bool), CheckOK μ env fe s₀ →
      (∀ a ∈ xs, P a s₀.store) → xs.allM f s₀ = .ok (b, s') →
      CoreStep μ env fe s₀ s' ∧ b = xs.all g := by
  intro xs
  induction xs with
  | nil =>
    intro s₀ s' b hok _ hrun
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | cons a as ih =>
    intro s₀ s' b hok hP hrun
    simp only [List.allM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hc⟩ := hf a s₀ s1 c hok (hP a (by simp)) k1
    cases c with
    | false =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      simp only [List.all_cons, ← hc, Bool.false_and]
    | true =>
      obtain ⟨p2, hb⟩ := ih s1 s' b p1.ok (fun x hx => hPx p1.ext (hP x (by simp [hx]))) z1
      refine ⟨p1.trans p2, ?_⟩
      simp only [List.all_cons, ← hc, Bool.true_and, hb]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm (the
projection-model conjunct's body) — one projection model looked up and its
level parameters compared. -/
theorem etaProjOk_run {μ : CheckMode} {env : Env} {fe' : IFEnv} {T : NIdx}
    {TP : ConLeche.Name} {lps : List NIdx} {lpsP : List ConLeche.Name} (j : Nat)
    {s₀ s' : AState} {b : Bool} (hok : CheckOK μ env fe' s₀)
    (hT : denoteN s₀.store.ns T = some TP)
    (hlps : Frontend.denoteNList s₀.store.ns lps = some lpsP)
    (hrun : (do
        match fe'.find? (← Arena.projModelName T j) with
        | some (.defnInfo cvmj _ _) => pure (cvmj.levelParams == lps)
        | _ => pure false : AM Bool) s₀ = .ok (b, s')) :
    CoreStep μ env fe' s₀ s' ∧
      b = (match env.find? (ConLeche.projModelName TP j) with
        | some (.defnInfo cvmj _ _) => cvmj.levelParams == lpsP
        | _ => false) := by
  obtain ⟨h, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hh⟩ := projModelName_run hok.state hT k1
  have c1 := p1.toCore hok
  cases hf : fe'.find? h with
  | none =>
    rw [hf] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨c1, ?_⟩
    rw [IFEnvOK.miss c1.ok.state c1.ok.ienv hh hf]
  | some ci =>
  obtain ⟨nm, c, hnm, hci, henv⟩ := c1.ok.ienv.hit h ci hf
  obtain rfl := Option.some.inj (hnm.symm.trans hh)
  have hk := denoteCI_kind hci
  rw [henv]
  cases ci
  case defnInfo cvmj v hint =>
    obtain ⟨cvmjP, vP, rfl, hcv, -⟩ := denoteCI_defn_inv hci
    rw [hf] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨c1, ?_⟩
    exact beq_nhandleList_eq c1.ok.state.wf (denoteCV_lps hcv)
      (denoteNListE_ext c1.ext _ _ hlps)
  all_goals
    (rw [hf] at z1
     obtain ⟨rfl, rfl⟩ := pureOk z1
     refine ⟨c1, ?_⟩
     cases c <;> simp [iciKind, ciKind] at hk ⊢)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
Is the block's eta theorem stored with the pinned statement?  PURE on
con-leche's side (a `Bool`), monadic here because the comparison reads the
store.

**CLOSED** (task #97-P3-Ind round 7): `checkUnitThm_spec`'s shape with a
third lookup, the projection models (`allM_cstep` over `etaProjOk_run`) and
the constructor-model right-hand side (`mapM_pstep` over the projection
applications, then `mkAppN_run`). -/
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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hC, hlps, hfe⟩ := hpre
  simp only [Arena.checkEtaThm] at hrun
  obtain ⟨tm, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok.state hT k1
  obtain ⟨etn, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hetn⟩ := internStrN_run p1.ok htm k2
  obtain ⟨cm, s2', k2', z2'⟩ := bindOk z2
  obtain ⟨p2', hcm⟩ := internStrN_run p2.ok (denoteN_ext hC (p1.ext.trans p2.ext)) k2'
  have c2 : CoreStep μ env fe' s₀ s2' := (p1.trans (p2.trans p2')).toCore hok
  have htm2 := denoteN_ext htm (p2.ext.trans p2'.ext)
  have hetn2 := denoteN_ext hetn p2'.ext
  have hlps2 := denoteNListE_ext c2.ext _ _ hlps
  have hT2 := denoteN_ext hT c2.ext
  -- the three lookups
  cases hf1 : fe'.find? etn with
  | none =>
    rw [hf1] at z2'
    obtain ⟨rfl, rfl⟩ := pureOk z2'
    refine ⟨c2, ?_⟩
    show false = _
    simp only [ConLeche.checkEtaThm, IFEnvOK.miss c2.ok.state c2.ok.ienv hetn2 hf1]
  | some ci1 =>
  obtain ⟨nm1, c1, hnm1, hci1, henv1⟩ := c2.ok.ienv.hit etn ci1 hf1
  obtain rfl := Option.some.inj (hnm1.symm.trans hetn2)
  have hk1 := denoteCI_kind hci1
  cases ci1
  case thmInfo tcv tv =>
    obtain ⟨tcvP, tvP, rfl, htcv, -⟩ := denoteCI_thm_inv hci1
    cases hf2 : fe'.find? tm with
    | none =>
      rw [hf1, hf2] at z2'
      obtain ⟨rfl, rfl⟩ := pureOk z2'
      refine ⟨c2, ?_⟩
      show false = _
      simp only [ConLeche.checkEtaThm, henv1, IFEnvOK.miss c2.ok.state c2.ok.ienv htm2 hf2]
    | some ci2 =>
    obtain ⟨nm2, c2P, hnm2, hci2, henv2⟩ := c2.ok.ienv.hit tm ci2 hf2
    obtain rfl := Option.some.inj (hnm2.symm.trans htm2)
    have hk2 := denoteCI_kind hci2
    cases ci2
    case defnInfo cvmT mv mh =>
      obtain ⟨cvmTP, mvP, rfl, hcvmT, -⟩ := denoteCI_defn_inv hci2
      cases hf3 : fe'.find? cm with
      | none =>
        rw [hf1, hf2, hf3] at z2'
        obtain ⟨rfl, rfl⟩ := pureOk z2'
        refine ⟨c2, ?_⟩
        show false = _
        simp only [ConLeche.checkEtaThm, henv1, henv2,
          IFEnvOK.miss c2.ok.state c2.ok.ienv hcm hf3]
      | some ci3 =>
      obtain ⟨nm3, c3P, hnm3, hci3, henv3⟩ := c2.ok.ienv.hit cm ci3 hf3
      obtain rfl := Option.some.inj (hnm3.symm.trans hcm)
      have hk3 := denoteCI_kind hci3
      cases ci3
      case defnInfo cvmC mcv mch =>
        obtain ⟨cvmCP, mcvP, rfl, hcvmC, -⟩ := denoteCI_defn_inv hci3
        rw [hf1, hf2, hf3] at z2'
        dsimp only at z2'
        obtain ⟨b, s3, k3, z3⟩ := bindOk z2'
        obtain ⟨c3, hb⟩ := eqBasisStored_spec fe' s2' s3 b c2.ok (denoteFEnv_ext c2.ext hfe) k3
        have hb' : b = decide (env.find? ConLeche.eqName = some ConLeche.eqA) := hb
        have c03 := c2.trans c3
        have hpure : ConLeche.checkEtaThm μ env TP ctorNameP lpsP nP nF =
            (match env.find? ConLeche.eqName with
             | some eqS => (eqS == ConLeche.eqA && tcvP.levelParams == lpsP &&
                 cvmTP.levelParams == lpsP && cvmCP.levelParams == lpsP &&
                 (List.range nF).all (fun j =>
                   match env.find? (ConLeche.projModelName TP j) with
                   | some (.defnInfo cvmj _ _) => cvmj.levelParams == lpsP
                   | _ => false) &&
                 (match tcvP.type.stripPis (nP + 1), cvmTP.type.stripPis nP with
                  | some (sbinders, sbody), some (tbindersM, tbodyM) =>
                    domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
                    (match sbinders[nP]? with
                     | some (xdom, _) =>
                       xdom == Expr.mkAppN (.const (TP.str "_model") (lpsP.map .param))
                         ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
                     | none => false) &&
                    (match sbody with
                     | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
                       c == ConLeche.eqName && lhsC == Expr.bvar 0 &&
                       tySlot == Expr.mkAppN (.const (TP.str "_model") (lpsP.map .param))
                         ((List.range nP).map fun k => Expr.bvar (nP - k)) &&
                       rhsC == Expr.mkAppN
                         (.const (ctorNameP.str "_model") (lpsP.map .param))
                         (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                          (List.range nF).map fun j => Expr.mkAppN
                            (.const (ConLeche.projModelName TP j) (lpsP.map .param))
                            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                             [Expr.bvar 0])) &&
                       (!μ.ttChecks || tbodyM == Expr.sort ℓA)
                     | _ => false)
                  | _, _ => false))
             | none => false) := by
          cases heq : env.find? ConLeche.eqName <;>
            simp only [ConLeche.checkEtaThm, henv1, henv2, henv3, heq] <;> rfl
        rw [hpure]
        cases b with
        | false =>
          simp only [Bool.not_false, if_true] at z3
          obtain ⟨rfl, rfl⟩ := pureOk z3
          refine ⟨c03, ?_⟩
          show false = _
          cases heq : env.find? ConLeche.eqName with
          | none => rfl
          | some eqS =>
            rw [heq] at hb'
            have hne : eqS ≠ ConLeche.eqA := by
              intro h; subst h; simp at hb'
            simp [hne]
        | true =>
        have heqA : env.find? ConLeche.eqName = some ConLeche.eqA := by
          simpa using hb'.symm
        simp only [heqA, beq_self_eq_true, Bool.true_and]
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at z3
        have hwf3 := c03.ok.state.wf
        have hlps3 := denoteNListE_ext c3.ext _ _ hlps2
        have hlpsE : (tcv.levelParams == lps && cvmT.levelParams == lps &&
            cvmC.levelParams == lps) =
            (tcvP.levelParams == lpsP && cvmTP.levelParams == lpsP &&
              cvmCP.levelParams == lpsP) := by
          rw [beq_nhandleList_eq hwf3 (denoteNListE_ext c3.ext _ _ (denoteCV_lps htcv)) hlps3,
            beq_nhandleList_eq hwf3 (denoteNListE_ext c3.ext _ _ (denoteCV_lps hcvmT)) hlps3,
            beq_nhandleList_eq hwf3 (denoteNListE_ext c3.ext _ _ (denoteCV_lps hcvmC)) hlps3]
        rw [hlpsE] at z3
        cases hlp : (tcvP.levelParams == lpsP && cvmTP.levelParams == lpsP &&
            cvmCP.levelParams == lpsP) with
        | false =>
          rw [hlp] at z3
          simp only [Bool.not_false, if_true] at z3
          obtain ⟨rfl, rfl⟩ := pureOk z3
          refine ⟨c03, ?_⟩
          show false = _
          rw [Bool.false_and, Bool.false_and]
        | true =>
        rw [hlp] at z3
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at z3
        rw [Bool.true_and]
        -- the projection models
        obtain ⟨po, s4, k4, z4⟩ := bindOk z3
        obtain ⟨c4, hpo⟩ := allM_cstep (fun _ st => denoteN st.ns T = some TP ∧
            Frontend.denoteNList st.ns lps = some lpsP)
          (fun hx h => ⟨denoteN_ext h.1 hx, denoteNListE_ext hx _ _ h.2⟩)
          (fun j s₀ s' b hok hP hrun => etaProjOk_run j hok hP.1 hP.2 hrun)
          (List.range nF) s3 s4 po c03.ok
          (fun _ _ => ⟨denoteN_ext hT2 c3.ext, hlps3⟩) k4
        have c04 := c03.trans c4
        rw [← hpo]
        cases po with
        | false =>
          simp only [Bool.not_false, if_true] at z4
          obtain ⟨rfl, rfl⟩ := pureOk z4
          exact ⟨c04, by simp⟩
        | true =>
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at z4
        rw [Bool.true_and]
        have htcv4 := denoteCV_ext htcv (c3.ext.trans c4.ext)
        have hcvmT4 := denoteCV_ext hcvmT (c3.ext.trans c4.ext)
        obtain ⟨sq1, s5, k5, z5⟩ := bindOk z4
        obtain ⟨hs5, hsq1⟩ := stripPis_pstep c04.ok.state (denoteCV_type htcv4) k5
        rw [hs5] at z5
        obtain ⟨sq2, s6, k6, z6⟩ := bindOk z5
        obtain ⟨hs6, hsq2⟩ := stripPis_pstep c04.ok.state (denoteCV_type hcvmT4) k6
        rw [hs6] at z6
        rcases sq1 with _ | ⟨sbs, sbody⟩
        · obtain ⟨rfl, rfl⟩ := pureOk z6
          refine ⟨c04, ?_⟩
          show false = _
          rw [stripPis_none hsq1]
        obtain ⟨sxs, sbodyP, hsps, hsbs, hsbody⟩ := denoteBP_someB hsq1
        rcases sq2 with _ | ⟨tbs, tbody⟩
        · obtain ⟨rfl, rfl⟩ := pureOk z6
          refine ⟨c04, ?_⟩
          show false = _
          rw [hsps, stripPis_none hsq2]
        obtain ⟨txs, tbodyP, htps, htbs, htbody⟩ := denoteBP_someB hsq2
        rw [hsps, htps]
        dsimp only
        dsimp only at z6
        have hwf4 := c04.ok.state.wf
        rw [domsMatchAux_eq hwf4 hsbs htbs] at z6
        cases hdm : ConLeche.domsMatchAux (fun _ e => e) sxs txs 0 0 nP with
        | false =>
          rw [hdm] at z6
          simp only [Bool.not_false, if_true] at z6
          obtain ⟨rfl, rfl⟩ := pureOk z6
          refine ⟨c04, ?_⟩
          show false = _
          simp
        | true =>
        rw [hdm] at z6
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at z6
        rw [Bool.true_and]
        -- the low family
        obtain ⟨us, s7, k7, z7⟩ := bindOk z6
        obtain ⟨q7, hus⟩ := paramLevels_spec lps lpsP s4 s7 us c04.ok.state
          (denoteNListE_ext c4.ext _ _ hlps3) k7
        obtain ⟨tHd, s8, k8, z8⟩ := bindOk z7
        obtain ⟨q8, htHd⟩ := internConstE_run q7.ok
          (denoteN_ext htm2 ((c3.ext.trans c4.ext).trans q7.ext)) hus k8
        obtain ⟨ps0, s9, k9, z9⟩ := bindOk z8
        obtain ⟨q9, hps0⟩ := structPsAt_spec 0 nP s8 s9 ps0 q8.ok trivial k9
        obtain ⟨fam0, s10, k10, z10⟩ := bindOk z9
        obtain ⟨q10, hfam0⟩ := mkAppN_run ps0 _ q9.ok (denote_ext htHd q9.ext) hps0 k10
        have e0 : ConLeche.structPsAt 0 nP =
            (List.range nP).map fun k => Expr.bvar (nP - 1 - k) :=
          bvarRange_congr (fun j => by omega)
        have e1 : ConLeche.structPsAt 1 nP =
            (List.range nP).map fun k => Expr.bvar (nP - k) :=
          bvarRange_congr (fun j => by omega)
        rw [e0] at hfam0
        have q4_10 : PStep s4 s10 := q7.trans (q8.trans (q9.trans q10))
        have c10 : CoreStep μ env fe' s₀ s10 := c04.trans (q4_10.toCore c04.ok)
        have hwf10 := q10.ok.wf
        have hsbs10 := denoteBinders_ext q4_10.ext _ _ hsbs
        obtain ⟨hX1, hX2⟩ := denoteBinders_getElem? hsbs10 nP
        have hfalse : ∀ {s₁ : AState}, CoreStep μ env fe' s₀ s₁ →
            (pure false : AM Bool) s₁ = .ok (r, s') →
            CoreStep μ env fe' s₀ s' ∧ r = false := by
          intro s₁ c h
          obtain ⟨rfl, rfl⟩ := pureOk h
          exact ⟨c, rfl⟩
        cases hx : sbs[nP]? with
        | none =>
          rw [hX2 hx]
          rw [hx] at z10
          obtain ⟨c, rfl⟩ := hfalse c10 (by simpa using z10)
          exact ⟨c, by simp⟩
        | some xb =>
        obtain ⟨xdom, xm⟩ := xb
        obtain ⟨xdomP, hxP, hxd⟩ := hX1 xdom xm hx
        rw [hxP]
        rw [hx] at z10
        dsimp only at z10
        replace z10 := AM.pure_bind_ok z10
        rw [beq_ehandle_eq hwf10 hxd hfam0] at z10
        dsimp only
        cases hxy : (xdomP == Expr.mkAppN (.const (TP.str "_model")
            (lpsP.map .param)) ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))) with
        | false =>
          rw [hxy] at z10
          obtain ⟨c, rfl⟩ := hfalse c10 (by simpa using z10)
          exact ⟨c, by simp⟩
        | true =>
        rw [hxy] at z10
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at z10
        rw [Bool.true_and]
        -- the high family and the equation
        obtain ⟨ps1, s11, k11, z11⟩ := bindOk z10
        obtain ⟨q11, hps1⟩ := structPsAt_spec 1 nP s10 s11 ps1 q10.ok trivial k11
        obtain ⟨fam1, s12, k12, z12⟩ := bindOk z11
        obtain ⟨q12, hfam1⟩ := mkAppN_run ps1 _ q11.ok
          (denote_ext htHd (q9.ext.trans (q10.ext.trans q11.ext))) hps1 k12
        rw [e1] at hfam1 hps1
        have hsbody12 := denote_ext hsbody (q4_10.ext.trans (q11.ext.trans q12.ext))
        obtain ⟨o, s13, k13, z13⟩ := bindOk z12
        obtain ⟨q13, ho⟩ := eqApp3?_spec sbody sbodyP s12 s13 o q12.ok hsbody12 k13
        obtain ⟨-, hon⟩ := eqApp3?_none sbody sbodyP s12 s13 o q12.ok hsbody12 k13
        have c13 : CoreStep μ env fe' s₀ s13 :=
          c10.trans ((q11.trans (q12.trans q13)).toCore c10.ok)
        cases o with
        | none =>
          obtain ⟨c, rfl⟩ := hfalse c13 (by simpa using z13)
          refine ⟨c, ?_⟩
          show false = _
          have hn := hon rfl
          split
          · exact absurd rfl (hn _ _ _ _ _)
          · rfl
        | some q =>
        obtain ⟨cc, lA, tySlot, lhsC, rhsC⟩ := q
        obtain ⟨ccP, lAP, tySlotP, lhsCP, rhsCP, hcc, hlA, htyS, hlhs, hrhs, hsb⟩ :=
          ho cc lA tySlot lhsC rhsC rfl
        dsimp only at z13
        obtain ⟨b0, s14, k14, z14⟩ := bindOk z13
        obtain ⟨q14, hb0⟩ := internBVarE_run q13.ok k14
        obtain ⟨cHd, s15, k15, z15⟩ := bindOk z14
        have x4_14 : Ext s4.store s14.store :=
          q4_10.ext.trans (q11.ext.trans (q12.ext.trans (q13.ext.trans q14.ext)))
        have hus14 : denoteLs s14.store.lss us = some (lpsP.map Level.param) :=
          denoteLs_ext hus (q8.ext.trans (q9.ext.trans (q10.ext.trans (q11.ext.trans
            (q12.ext.trans (q13.ext.trans q14.ext))))))
        obtain ⟨q15, hcHd⟩ := internConstE_run q14.ok
          (denoteN_ext hcm ((c3.ext.trans c4.ext).trans x4_14)) hus14 k15
        obtain ⟨pas, s16, k16, z16⟩ := bindOk z15
        have hT15 : denoteN s15.store.ns T = some TP :=
          denoteN_ext hT2 (((c3.ext.trans c4.ext).trans x4_14).trans q15.ext)
        have hus15 := denoteLs_ext hus14 q15.ext
        have hps15 := denoteEList_ext ((q12.ext.trans (q13.ext.trans q14.ext)).trans q15.ext)
          _ _ hps1
        have hb015 := denote_ext hb0 q15.ext
        obtain ⟨q16, hpas⟩ := mapM_pstep
          (fun j => (do
            let pHd ← internE (.const (← Arena.projModelName T j) us)
            Arena.mkAppN pHd (ps1 ++ [b0]) : AM EIdx))
          (fun j => Expr.mkAppN (.const (ConLeche.projModelName TP j) (lpsP.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++ [Expr.bvar 0]))
          (fun st b c => denoteE st b = some c)
          (fun _ st => denoteN st.ns T = some TP ∧
            denoteLs st.lss us = some (lpsP.map Level.param) ∧
            Frontend.denoteEList st ps1 = some ((List.range nP).map fun k => Expr.bvar (nP - k)) ∧
            denoteE st b0 = some (.bvar 0))
          (fun hx h => denote_ext h hx)
          (fun hx h => ⟨denoteN_ext h.1 hx, denoteLs_ext h.2.1 hx,
            denoteEList_ext hx _ _ h.2.2.1, denote_ext h.2.2.2 hx⟩)
          (by
            intro j t₀ t' b hokt hP hrun
            obtain ⟨hTt, hust, hpst, hb0t⟩ := hP
            obtain ⟨nmh, t1, g1, y1⟩ := bindOk hrun
            obtain ⟨r1, hnmh⟩ := projModelName_run hokt hTt g1
            obtain ⟨pHd, t2, g2, y2⟩ := bindOk y1
            obtain ⟨r2, hpHd⟩ := internConstE_run r1.ok hnmh (denoteLs_ext hust r1.ext) g2
            obtain ⟨r3, hr⟩ := mkAppN_run _ _ r2.ok hpHd
              (denoteEList_append (denoteEList_ext (r1.ext.trans r2.ext) _ _ hpst)
                (show Frontend.denoteEList t2.store [b0] = some [Expr.bvar 0] by
                  simp [Frontend.denoteEList, denote_ext hb0t (r1.ext.trans r2.ext)]))
              y2
            exact ⟨r1.trans (r2.trans r3), hr⟩)
          (List.range nF) s15 s16 pas q15.ok (fun _ _ => ⟨hT15, hus15, hps15, hb015⟩) k16
        have hpasE := ListRel.toEList hpas
        obtain ⟨want, s17, k17, z17⟩ := bindOk z16
        obtain ⟨q17, hwant⟩ := mkAppN_run _ _ q16.ok (denote_ext hcHd q16.ext)
          (denoteEList_append (denoteEList_ext q16.ext _ _ hps15) hpasE) k17
        obtain ⟨sortA, s18, k18, z18⟩ := bindOk z17
        obtain ⟨q18, hsortA⟩ := internSortE_run q17.ok
          (denoteL_ext hlA (q14.ext.trans (q15.ext.trans (q16.ext.trans q17.ext)))) k18
        have q13_18 : PStep s13 s18 := q14.trans (q15.trans (q16.trans (q17.trans q18)))
        have c18 : CoreStep μ env fe' s₀ s18 := c13.trans (q13_18.toCore c13.ok)
        obtain ⟨pe, s19, k19, z19⟩ := bindOk z18
        obtain ⟨hs19, hpe⟩ := pinAt_run (x := ConLeche.eqName) c18.ok.pins rfl k19
        rw [hs19] at z19
        obtain ⟨rfl, rfl⟩ := pureOk z19
        refine ⟨c18, ?_⟩
        have hwf18 := c18.ok.state.wf
        have x13 : Ext s13.store s'.store := q13_18.ext
        subst hsb
        show (cc == pe && lhsC == b0 && tySlot == fam1 && rhsC == want &&
          (!μ.ttChecks || tbody == sortA)) = _
        rw [beq_handle_eq hwf18 (denoteN_ext hcc x13) hpe,
          beq_ehandle_eq hwf18 (denote_ext hlhs x13)
            (denote_ext hb0 (q15.ext.trans (q16.ext.trans (q17.ext.trans q18.ext)))),
          beq_ehandle_eq hwf18 (denote_ext htyS x13) (denote_ext hfam1 (q13.ext.trans x13)),
          beq_ehandle_eq hwf18 (denote_ext hrhs x13) (denote_ext hwant q18.ext),
          beq_ehandle_eq hwf18 (denote_ext htbody (x4_14.trans
            (q15.ext.trans (q16.ext.trans (q17.ext.trans q18.ext))))) hsortA]
      all_goals
        (rw [hf1, hf2, hf3] at z2'
         obtain ⟨rfl, rfl⟩ := pureOk z2'
         refine ⟨c2, ?_⟩
         show false = _
         simp only [ConLeche.checkEtaThm, henv1, henv2, henv3]
         cases c3P <;> simp [iciKind, ciKind] at hk3 ⊢)
    all_goals
      (rw [hf1, hf2] at z2'
       obtain ⟨rfl, rfl⟩ := pureOk z2'
       refine ⟨c2, ?_⟩
       show false = _
       simp only [ConLeche.checkEtaThm, henv1, henv2]
       cases c2P <;> simp [iciKind, ciKind] at hk2 ⊢)
  all_goals
    (rw [hf1] at z2'
     obtain ⟨rfl, rfl⟩ := pureOk z2'
     refine ⟨c2, ?_⟩
     show false = _
     simp only [ConLeche.checkEtaThm, henv1]
     cases c1 <;> simp [iciKind, ciKind] at hk1 ⊢)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
The unit-likeness theorem, the same way.

**CLOSED** (task #97-P3-Ind round 7): `IFEnvOK.find_thm`/`find_defn` and
`denoteCI_kind` for the two lookups (the fallthrough arm is the same arm on
both sides), `eqBasisStored_spec`, `beq_nhandleList_eq` for the level lists,
`stripPis_pstep` twice, `domsMatchAux_eq`, `paramLevels_spec`,
`structPsAt_spec` and `mkAppN_run` for the three families, and
`eqApp3?_spec`/`eqApp3?_none` for the equation — every handle comparison one
`beq_ehandle_eq`. -/
theorem checkUnitThm_spec {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP : Nat) :
    CSpec μ env fe'
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteFEnv st fe' = some env)
      (Arena.checkUnitThm μ fe' T lps nP)
      (RV (ConLeche.checkUnitThm μ env TP lpsP nP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hfe⟩ := hpre
  simp only [Arena.checkUnitThm] at hrun
  obtain ⟨tm, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, htm⟩ := internStrN_run hok.state hT k1
  obtain ⟨utn, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hutn⟩ := internStrN_run p1.ok htm k2
  have c2 : CoreStep μ env fe' s₀ s2 := (p1.trans p2).toCore hok
  have htm2 := denoteN_ext htm p2.ext
  have hlps2 := denoteNListE_ext c2.ext _ _ hlps
  -- the two lookups
  cases hf1 : fe'.find? utn with
  | none =>
    rw [hf1] at z2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c2, ?_⟩
    show false = _
    simp only [ConLeche.checkUnitThm, IFEnvOK.miss c2.ok.state c2.ok.ienv hutn hf1]
  | some ci1 =>
  obtain ⟨nm1, c1, hnm1, hci1, henv1⟩ := c2.ok.ienv.hit utn ci1 hf1
  obtain rfl := Option.some.inj (hnm1.symm.trans hutn)
  have hk1 := denoteCI_kind hci1
  cases ci1
  case thmInfo tcv tv =>
    obtain ⟨tcvP, tvP, rfl, htcv, -⟩ := denoteCI_thm_inv hci1
    cases hf2 : fe'.find? tm with
    | none =>
      rw [hf1, hf2] at z2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨c2, ?_⟩
      show false = _
      simp only [ConLeche.checkUnitThm, henv1, IFEnvOK.miss c2.ok.state c2.ok.ienv htm2 hf2]
    | some ci2 =>
    obtain ⟨nm2, c2P, hnm2, hci2, henv2⟩ := c2.ok.ienv.hit tm ci2 hf2
    obtain rfl := Option.some.inj (hnm2.symm.trans htm2)
    have hk2 := denoteCI_kind hci2
    cases ci2
    case defnInfo cvmT mv mh =>
      obtain ⟨cvmTP, mvP, rfl, hcvmT, -⟩ := denoteCI_defn_inv hci2
      rw [hf1, hf2] at z2
      dsimp only at z2
      obtain ⟨b, s3, k3, z3⟩ := bindOk z2
      obtain ⟨c3, hb⟩ := eqBasisStored_spec fe' s2 s3 b c2.ok (denoteFEnv_ext c2.ext hfe) k3
      have hb' : b = decide (env.find? ConLeche.eqName = some ConLeche.eqA) := hb
      have c03 := c2.trans c3
      -- the pure side, its lookups done
      have hpure : ConLeche.checkUnitThm μ env TP lpsP nP =
          (match env.find? ConLeche.eqName with
           | some eqS => (eqS == ConLeche.eqA && tcvP.levelParams == lpsP &&
               cvmTP.levelParams == lpsP &&
               (match tcvP.type.stripPis (nP + 2), cvmTP.type.stripPis nP with
                | some (sbinders, sbody), some (tbindersM, tbodyM) =>
                  domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
                  (match sbinders[nP]? with
                   | some (xdom, _) =>
                     xdom == Expr.mkAppN (.const (TP.str "_model") (lpsP.map .param))
                       ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
                   | none => false) &&
                  (match sbinders[nP + 1]? with
                   | some (ydom, _) =>
                     ydom == Expr.mkAppN (.const (TP.str "_model") (lpsP.map .param))
                       ((List.range nP).map fun k => Expr.bvar (nP - k))
                   | none => false) &&
                  (match sbody with
                   | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
                     c == ConLeche.eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0 &&
                     tySlot == Expr.mkAppN (.const (TP.str "_model") (lpsP.map .param))
                       ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) &&
                     (!μ.ttChecks || tbodyM == Expr.sort ℓA)
                   | _ => false)
                | _, _ => false))
           | none => false) := by
        cases heq : env.find? ConLeche.eqName <;>
          simp only [ConLeche.checkUnitThm, henv1, henv2, heq] <;> rfl
      rw [hpure]
      cases b with
      | false =>
        simp only [Bool.not_false, if_true] at z3
        obtain ⟨rfl, rfl⟩ := pureOk z3
        refine ⟨c03, ?_⟩
        show false = _
        cases heq : env.find? ConLeche.eqName with
        | none => rfl
        | some eqS =>
          rw [heq] at hb'
          have hne : eqS ≠ ConLeche.eqA := by
            intro h; subst h; simp at hb'
          simp [hne]
      | true =>
      have heqA : env.find? ConLeche.eqName = some ConLeche.eqA := by
        simpa using hb'.symm
      simp only [heqA, beq_self_eq_true, Bool.true_and]
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at z3
      have hwf3 := c03.ok.state.wf
      have hlpsE : (tcv.levelParams == lps && cvmT.levelParams == lps) =
          (tcvP.levelParams == lpsP && cvmTP.levelParams == lpsP) := by
        rw [beq_nhandleList_eq hwf3 (denoteNListE_ext c3.ext _ _ (denoteCV_lps htcv))
            (denoteNListE_ext c3.ext _ _ hlps2),
          beq_nhandleList_eq hwf3 (denoteNListE_ext c3.ext _ _ (denoteCV_lps hcvmT))
            (denoteNListE_ext c3.ext _ _ hlps2)]
      rw [hlpsE] at z3
      cases hlp : (tcvP.levelParams == lpsP && cvmTP.levelParams == lpsP) with
      | false =>
        rw [hlp] at z3
        simp only [Bool.not_false, if_true] at z3
        obtain ⟨rfl, rfl⟩ := pureOk z3
        refine ⟨c03, ?_⟩
        show false = _
        rw [Bool.false_and]
      | true =>
      rw [hlp] at z3
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at z3
      rw [Bool.true_and]
      have htcv3 := denoteCV_ext htcv c3.ext
      have hcvmT3 := denoteCV_ext hcvmT c3.ext
      obtain ⟨sq1, s4, k4, z4⟩ := bindOk z3
      obtain ⟨hs4, hsq1⟩ := stripPis_pstep c03.ok.state (denoteCV_type htcv3) k4
      rw [hs4] at z4
      obtain ⟨sq2, s5, k5, z5⟩ := bindOk z4
      obtain ⟨hs5, hsq2⟩ := stripPis_pstep c03.ok.state (denoteCV_type hcvmT3) k5
      rw [hs5] at z5
      rcases sq1 with _ | ⟨sbs, sbody⟩
      · obtain ⟨rfl, rfl⟩ := pureOk z5
        refine ⟨c03, ?_⟩
        show false = _
        rw [stripPis_none hsq1]
      obtain ⟨sxs, sbodyP, hsps, hsbs, hsbody⟩ := denoteBP_someB hsq1
      rcases sq2 with _ | ⟨tbs, tbody⟩
      · obtain ⟨rfl, rfl⟩ := pureOk z5
        refine ⟨c03, ?_⟩
        show false = _
        rw [hsps, stripPis_none hsq2]
      obtain ⟨txs, tbodyP, htps, htbs, htbody⟩ := denoteBP_someB hsq2
      rw [hsps, htps]
      dsimp only
      dsimp only at z5
      rw [domsMatchAux_eq hwf3 hsbs htbs] at z5
      cases hdm : ConLeche.domsMatchAux (fun _ e => e) sxs txs 0 0 nP with
      | false =>
        rw [hdm] at z5
        simp only [Bool.not_false, if_true] at z5
        obtain ⟨rfl, rfl⟩ := pureOk z5
        refine ⟨c03, ?_⟩
        show false = _
        simp
      | true =>
      rw [hdm] at z5
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at z5
      rw [Bool.true_and]
      -- the three families
      obtain ⟨us, s6, k6, z6⟩ := bindOk z5
      obtain ⟨q6, hus⟩ := paramLevels_spec lps lpsP s3 s6 us c03.ok.state
        (denoteNListE_ext c3.ext _ _ hlps2) k6
      obtain ⟨tHd, s7, k7, z7⟩ := bindOk z6
      obtain ⟨q7, htHd⟩ := internConstE_run q6.ok
        (denoteN_ext htm2 (c3.ext.trans q6.ext)) hus k7
      obtain ⟨ps0, s8, k8, z8⟩ := bindOk z7
      obtain ⟨q8, hps0⟩ := structPsAt_spec 0 nP s7 s8 ps0 q7.ok trivial k8
      obtain ⟨fam0, s9, k9, z9⟩ := bindOk z8
      obtain ⟨q9, hfam0⟩ := mkAppN_run ps0 _ q8.ok (denote_ext htHd q8.ext) hps0 k9
      obtain ⟨ps1, s10, k10, z10⟩ := bindOk z9
      obtain ⟨q10, hps1⟩ := structPsAt_spec 1 nP s9 s10 ps1 q9.ok trivial k10
      obtain ⟨fam1, s11, k11, z11⟩ := bindOk z10
      obtain ⟨q11, hfam1⟩ := mkAppN_run ps1 _ q10.ok
        (denote_ext htHd (q8.ext.trans (q9.ext.trans q10.ext))) hps1 k11
      obtain ⟨ps2, s12, k12, z12⟩ := bindOk z11
      obtain ⟨q12, hps2⟩ := structPsAt_spec 2 nP s11 s12 ps2 q11.ok trivial k12
      obtain ⟨fam2, s13, k13, z13⟩ := bindOk z12
      obtain ⟨q13, hfam2⟩ := mkAppN_run ps2 _ q12.ok
        (denote_ext htHd (q8.ext.trans (q9.ext.trans (q10.ext.trans (q11.ext.trans
          q12.ext))))) hps2 k13
      have q3_13 : PStep s3 s13 := q6.trans (q7.trans (q8.trans (q9.trans (q10.trans
        (q11.trans (q12.trans q13))))))
      have hwf13 := q13.ok.wf
      have e0 : ConLeche.structPsAt 0 nP = (List.range nP).map fun k => Expr.bvar (nP - 1 - k) :=
        bvarRange_congr (fun j => by omega)
      have e1 : ConLeche.structPsAt 1 nP = (List.range nP).map fun k => Expr.bvar (nP - k) :=
        bvarRange_congr (fun j => by omega)
      have e2 : ConLeche.structPsAt 2 nP = (List.range nP).map fun k => Expr.bvar (nP + 1 - k) :=
        bvarRange_congr (fun j => by omega)
      rw [e0] at hfam0; rw [e1] at hfam1; rw [e2] at hfam2
      have hfam0' := denote_ext hfam0 (q10.ext.trans (q11.ext.trans (q12.ext.trans q13.ext)))
      have hfam1' := denote_ext hfam1 (q12.ext.trans q13.ext)
      have hsbs13 := denoteBinders_ext q3_13.ext _ _ hsbs
      obtain ⟨hX1, hX2⟩ := denoteBinders_getElem? hsbs13 nP
      obtain ⟨hY1, hY2⟩ := denoteBinders_getElem? hsbs13 (nP + 1)
      -- the two binder checks, four ways
      have hfalse : ∀ {s₁ : AState}, CoreStep μ env fe' s₀ s₁ →
          (pure false : AM Bool) s₁ = .ok (r, s') →
          CoreStep μ env fe' s₀ s' ∧ r = false := by
        intro s₁ c h
        obtain ⟨rfl, rfl⟩ := pureOk h
        exact ⟨c, rfl⟩
      have c13 : CoreStep μ env fe' s₀ s13 := c03.trans (q3_13.toCore c03.ok)
      cases hx : sbs[nP]? with
      | none =>
        rw [hX2 hx]
        rw [hx] at z13
        cases hy : sbs[nP + 1]? with
        | none =>
          rw [hy] at z13
          obtain ⟨c, rfl⟩ := hfalse c13 (by simpa using z13)
          exact ⟨c, by simp⟩
        | some yb =>
          rw [hy] at z13
          obtain ⟨c, rfl⟩ := hfalse c13 (by simpa using z13)
          exact ⟨c, by simp⟩
      | some xb =>
      obtain ⟨xdom, xm⟩ := xb
      obtain ⟨xdomP, hxP, hxd⟩ := hX1 xdom xm hx
      rw [hxP]
      rw [hx] at z13
      dsimp only at z13
      have ex : (xdom == fam0) = (xdomP == Expr.mkAppN (.const (TP.str "_model")
          (lpsP.map .param)) ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))) :=
        beq_ehandle_eq hwf13 hxd hfam0'
      cases hy : sbs[nP + 1]? with
      | none =>
        rw [hY2 hy]
        rw [hy] at z13
        obtain ⟨c, rfl⟩ := hfalse c13 (by simpa using z13)
        exact ⟨c, by simp⟩
      | some yb =>
      obtain ⟨ydom, ym⟩ := yb
      obtain ⟨ydomP, hyP, hyd⟩ := hY1 ydom ym hy
      rw [hyP]
      rw [hy] at z13
      dsimp only at z13
      have ey : (ydom == fam1) = (ydomP == Expr.mkAppN (.const (TP.str "_model")
          (lpsP.map .param)) ((List.range nP).map fun k => Expr.bvar (nP - k))) :=
        beq_ehandle_eq hwf13 hyd hfam1'
      rw [ex, ey] at z13
      replace z13 := AM.pure_bind_ok z13
      replace z13 := AM.pure_bind_ok z13
      dsimp only
      cases hxy : (xdomP == Expr.mkAppN (.const (TP.str "_model")
          (lpsP.map .param)) ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)) &&
          ydomP == Expr.mkAppN (.const (TP.str "_model")
          (lpsP.map .param)) ((List.range nP).map fun k => Expr.bvar (nP - k))) with
      | false =>
        rw [hxy] at z13
        obtain ⟨c, rfl⟩ := hfalse c13 (by simpa using z13)
        refine ⟨c, ?_⟩
        show false = _
        simp
      | true =>
      rw [hxy] at z13
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at z13
      rw [Bool.true_and]
      -- the equation
      have hsbody13 := denote_ext hsbody q3_13.ext
      obtain ⟨o, s14, k14, z14⟩ := bindOk z13
      obtain ⟨q14, ho⟩ := eqApp3?_spec sbody sbodyP s13 s14 o q13.ok hsbody13 k14
      obtain ⟨q14', hon⟩ := eqApp3?_none sbody sbodyP s13 s14 o q13.ok hsbody13 k14
      cases o with
      | none =>
        obtain ⟨c, rfl⟩ := hfalse (c13.trans (q14.toCore c13.ok)) (by simpa using z14)
        refine ⟨c, ?_⟩
        show false = _
        have hn := hon rfl
        split
        · exact absurd rfl (hn _ _ _ _ _)
        · rfl
      | some q =>
      obtain ⟨cc, lA, tySlot, lhsC, rhsC⟩ := q
      obtain ⟨ccP, lAP, tySlotP, lhsCP, rhsCP, hcc, hlA, htyS, hlhs, hrhs, hsb⟩ :=
        ho cc lA tySlot lhsC rhsC rfl
      dsimp only at z14
      obtain ⟨b0, s15, k15, z15⟩ := bindOk z14
      obtain ⟨q15, hb0⟩ := internBVarE_run q14.ok k15
      obtain ⟨b1, s16, k16, z16⟩ := bindOk z15
      obtain ⟨q16, hb1⟩ := internBVarE_run q15.ok k16
      obtain ⟨sortA, s17, k17, z17⟩ := bindOk z16
      obtain ⟨q17, hsortA⟩ := internSortE_run q16.ok
        (denoteL_ext hlA (q15.ext.trans q16.ext)) k17
      obtain ⟨pe, s18, k18, z18⟩ := bindOk z17
      obtain ⟨hs18, hpe⟩ := pinAt_run (x := ConLeche.eqName)
        (((c13.trans (q14.toCore c13.ok)).trans
          ((q15.trans (q16.trans q17)).toCore (c13.trans (q14.toCore c13.ok)).ok)).ok.pins)
        rfl k18
      rw [hs18] at z18
      obtain ⟨rfl, rfl⟩ := pureOk z18
      have q14_17 : PStep s14 s' := q15.trans (q16.trans q17)
      have c17 : CoreStep μ env fe' s₀ s' :=
        (c13.trans (q14.toCore c13.ok)).trans (q14_17.toCore (c13.trans (q14.toCore c13.ok)).ok)
      refine ⟨c17, ?_⟩
      have hwf17 := c17.ok.state.wf
      have x14 : Ext s14.store s'.store := q14_17.ext
      have x1317 : Ext s13.store s'.store := q14.ext.trans x14
      subst hsb
      show (cc == pe && lhsC == b1 && rhsC == b0 && tySlot == fam2 &&
        (!μ.ttChecks || tbody == sortA)) = _
      rw [beq_handle_eq hwf17 (denoteN_ext hcc x14) hpe,
        beq_ehandle_eq hwf17 (denote_ext hlhs x14)
          (denote_ext hb1 q17.ext),
        beq_ehandle_eq hwf17 (denote_ext hrhs x14)
          (denote_ext hb0 (q16.ext.trans q17.ext)),
        beq_ehandle_eq hwf17 (denote_ext htyS x14) (denote_ext hfam2 x1317),
        beq_ehandle_eq hwf17 (denote_ext htbody (q3_13.ext.trans x1317))
          hsortA]
    all_goals
      (rw [hf1, hf2] at z2
       obtain ⟨rfl, rfl⟩ := pureOk z2
       refine ⟨c2, ?_⟩
       show false = _
       simp only [ConLeche.checkUnitThm, henv1, henv2]
       cases c2P <;> simp [iciKind, ciKind] at hk2 ⊢)
  all_goals
    (rw [hf1] at z2
     obtain ⟨rfl, rfl⟩ := pureOk z2
     refine ⟨c2, ?_⟩
     show false = _
     simp only [ConLeche.checkUnitThm, henv1]
     cases c1 <;> simp [iciKind, ciKind] at hk1 ⊢)

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
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (hcoh : IFEnvCoh e)
    (T ctorName : NIdx)
    (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF i : Nat) :
    ISpec
      (fun s => ReadOK env e s ∧ denoteN s.store.ns T = some TP ∧
        denoteN s.store.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList s.store.ns lps = some lpsP ∧
        denoteFEnv s.store e = some env)
      (Arena.installProjFnStep μ T ctorName lps nP nF e i)
      (fun s r => InstRel e (fun x => (∃ F, ConLeche.installProjFnStep
        μ (ConLeche.fueledOps μ F) TP ctorNameP lpsP nP nF env i = .ok x) ∧
        ReadOK x r s) s.store r) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
`installProjFns` is the twin's explicit recursion for con-leche's third
`foldlM` (deviation 3).

`sorry`: a `Nat` recursion over `installProjFnStep_spec` and `InstRel.trans`. -/
theorem installProjFns_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (hcoh : IFEnvCoh fe)
    (T ctorName : NIdx)
    (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF k i : Nat) :
    ISpec
      (fun s => ReadOK env fe s ∧ denoteN s.store.ns T = some TP ∧
        denoteN s.store.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList s.store.ns lps = some lpsP ∧
        denoteFEnv s.store fe = some env)
      (Arena.installProjFns μ T ctorName lps nP nF fe k i)
      (fun s r => InstRel fe (fun x => (∃ F,
        (List.range k).foldlM (fun e j => ConLeche.installProjFnStep
          μ (ConLeche.fueledOps μ F) TP ctorNameP lpsP nP nF e (i + j)) env
          = .ok x) ∧ ReadOK x r s) s.store r) := by
  sorry

/-! ## The capability record and the route -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:55-62 piResultIsProp — **in run
form** (task #97-P3-Ind round 7, on loan from the Core tier): `piResult_spec`,
one `view`, the zero pin and `lvlEq?_spec`'s verdict. -/
theorem piResultIsProp_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s₀ s' : AState}
    {e : EIdx} {eP : Expr} {b : Bool} (hok : CheckOK μ env fe s₀)
    (he : denoteE s₀.store e = some eP)
    (hrun : Arena.piResultIsProp e s₀ = .ok (b, s')) :
    CoreStep μ env fe s₀ s' ∧ b = ConLeche.piResultIsProp eP := by
  simp only [Arena.piResultIsProp] at hrun
  obtain ⟨pr, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hpr⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
    (ExprOps.piResult_spec Arena.coreWalkFuel s₀ e hok.state (by rw [he]; rfl))
  rw [hs1] at z1
  have hprd := hpr eP he
  obtain ⟨v, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hv⟩ := view_run k2
  rw [hs2] at z2
  cases v
  case sort u =>
    obtain ⟨uP, hPe, hu⟩ := denote_sort_inv hok.state.wf hv hprd
    obtain ⟨z, s3, k3, z3⟩ := bindOk z2
    obtain ⟨hs3, hz⟩ := zeroLevel_run hok.pins k3
    rw [hs3] at z3
    obtain ⟨vv, s4, k4, z4⟩ := bindOk z3
    obtain ⟨hok4, hst4, hp4, lu, lz, hlu, hlz, hvv⟩ :=
      AM.of_run (P := fun t => t = s₀) rfl k4 (Core.lvlEq?_spec s₀ u z hok)
    obtain ⟨rfl, rfl⟩ := pureOk z4
    refine ⟨⟨hok4, by rw [hst4]; exact Ext.refl _, hp4⟩, ?_⟩
    rw [hu] at hlu; rw [hz] at hlz
    cases hlu; cases hlz
    simp only [ConLeche.piResultIsProp, hPe, hvv]
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk z2
     refine ⟨CoreStep.refl hok, ?_⟩
     rw [denoteE_view_eq hok.state.wf hv] at hprd
     simp only [ConLeche.piResultIsProp]
     split
     · rename_i u hPe; rw [hPe] at hprd; simp [denoteEView] at hprd
     · rfl)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:64-72 piResultZ — **in run
form**: `piResult_spec`, one `view` and `readLevelM` (a `ReadbackFrame`). -/
theorem piResultZ_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s₀ s' : AState}
    {e : EIdx} {eP : Expr} {z : PropWhen} (hok : CheckOK μ env fe s₀)
    (he : denoteE s₀.store e = some eP)
    (hrun : Arena.piResultZ e s₀ = .ok (z, s')) :
    CoreStep μ env fe s₀ s' ∧ z = ConLeche.piResultZ eP := by
  simp only [Arena.piResultZ] at hrun
  obtain ⟨pr, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hpr⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
    (ExprOps.piResult_spec Arena.coreWalkFuel s₀ e hok.state (by rw [he]; rfl))
  rw [hs1] at z1
  have hprd := hpr eP he
  obtain ⟨v, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hv⟩ := view_run k2
  rw [hs2] at z2
  cases v
  case sort u =>
    obtain ⟨uP, hPe, hu⟩ := denote_sort_inv hok.state.wf hv hprd
    obtain ⟨l, s3, k3, z3⟩ := bindOk z2
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := AM.of_run (P := fun t => t = s₀) rfl k3
      (readLevelM_spec s₀ u hok.caches.readL)
    have hfr := Core.ReadbackFrame.ofReadL h1 h2 h3 h4 h6
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨⟨Core.CheckOK.ofReadbackFrame hok hfr, hfr.ext, hfr.pins⟩, ?_⟩
    rw [hu] at h5; cases h5
    simp only [ConLeche.piResultZ, hPe]
  all_goals
    (obtain ⟨rfl, rfl⟩ := pureOk z2
     refine ⟨CoreStep.refl hok, ?_⟩
     rw [denoteE_view_eq hok.state.wf hv] at hprd
     simp only [ConLeche.piResultZ]
     split
     · rename_i u hPe; rw [hPe] at hprd; simp [denoteEView] at hprd
     · rfl)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:724-735 indBlockCaps
The block's capability record: eta and unit-likeness off the two theorems,
rule K off the shape.

**CLOSED** (task #97-P3-Ind round 7): `checkEtaThm_spec`, `checkUnitThm_spec`,
`piResultIsProp_run` and `piResultZ_run` (both new, on loan from the Core
tier), and `Frontend.denoteCaps` at the answer. -/
theorem indBlockCaps_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (cvT cvC : IConstantVal) (cvTP cvCP : ConstantVal) (nP nF : Nat) :
    CSpec μ env fe
      (fun st => Frontend.denoteCV st cvT = some cvTP ∧
        Frontend.denoteCV st cvC = some cvCP ∧ denoteFEnv st fe = some env)
      (Arena.indBlockCaps μ fe cvT cvC nP nF)
      (RCaps (ConLeche.indBlockCaps μ env cvTP cvCP nP nF)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hcvT, hcvC, hfe⟩ := hpre
  simp only [Arena.indBlockCaps] at hrun
  obtain ⟨be, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨c1, hbe⟩ := checkEtaThm_spec fe cvT.name cvC.name cvTP.name cvCP.name
    cvT.levelParams cvTP.levelParams nP nF s₀ s1 be hok
    ⟨denoteCV_name hcvT, denoteCV_name hcvC, denoteCV_lps hcvT, hfe⟩ k1
  obtain ⟨bu, s2, k2, z2⟩ := bindOk z1
  obtain ⟨c2, hbu⟩ := checkUnitThm_spec fe cvT.name cvTP.name cvT.levelParams
    cvTP.levelParams nP s1 s2 bu c1.ok
    ⟨denoteN_ext (denoteCV_name hcvT) c1.ext, denoteNListE_ext c1.ext _ _ (denoteCV_lps hcvT),
      denoteFEnv_ext c1.ext hfe⟩ k2
  have c12 := c1.trans c2
  obtain ⟨bk, s3, k3, z3⟩ := bindOk z2
  obtain ⟨c3, hbk⟩ := piResultIsProp_run c12.ok (denote_ext (denoteCV_type hcvT) c12.ext) k3
  have c13 := c12.trans c3
  obtain ⟨bz, s4, k4, z4⟩ := bindOk z3
  obtain ⟨c4, hbz⟩ := piResultZ_run c13.ok (denote_ext (denoteCV_type hcvT) c13.ext) k4
  obtain ⟨rfl, rfl⟩ := pureOk z4
  refine ⟨c13.trans c4, ?_⟩
  have hbe' : be = ConLeche.checkEtaThm μ env cvTP.name cvCP.name cvTP.levelParams nP nF := hbe
  have hbu' : bu = ConLeche.checkUnitThm μ env cvTP.name cvTP.levelParams nP := hbu
  have hwf := (c13.trans c4).ok.state.wf
  have hx := (c13.trans c4).ext
  have hlpe : decide (cvC.levelParams = cvT.levelParams) =
      decide (cvCP.levelParams = cvTP.levelParams) := by
    have h := beq_nhandleList_eq hwf (denoteNListE_ext hx _ _ (denoteCV_lps hcvC))
      (denoteNListE_ext hx _ _ (denoteCV_lps hcvT))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← beq_iff_eq, h, beq_iff_eq]
  show Frontend.denoteCaps _ _ = _
  simp only [Frontend.denoteCaps, denoteN_ext (denoteCV_name hcvC) hx, ConLeche.indBlockCaps,
    hbe', hbu', hbk, hbz, hlpe]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
The eta capability's constructor returns the family (task #136).

**CLOSED** (task #97-P3-Ind round 5): the capability guard, `IFEnvOK`'s
`hit`/`miss` pair at the stored constructor — the check reads the constant the
way its consumers do, which is what makes the `find?` load-bearing —
`stripPis_pstep`, `structFam_spec` and `beq_ehandle_eq`.  The six
non-constructor kinds close on `denoteCI_not_ctor`: `denoteCI` preserves the
kind, so the arena's fallthrough arm and con-leche's are the same arm. -/
theorem ctorResidualOk_run {μ : CheckMode} {env : Env} (fe' : IFEnv)
    (T ctorName : NIdx) (TP ctorNameP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) (eta : Bool) :
    ∀ (s₀ s' : AState) (r : Bool), ReadOK env fe' s₀ →
      (denoteN s₀.store.ns T = some TP ∧
        denoteN s₀.store.ns ctorName = some ctorNameP ∧
        Frontend.denoteNList s₀.store.ns lps = some lpsP) →
      Arena.ctorResidualOk μ fe' T ctorName lps nP nF eta s₀ = .ok (r, s') →
      PStep s₀ s' ∧ r = ConLeche.ctorResidualOk μ env TP ctorNameP lpsP nP nF eta := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hT, hct, hlps⟩ := hpre
  simp only [Arena.ctorResidualOk] at hrun
  split at hrun
  case isTrue hg =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hck.state, ?_⟩
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
      refine ⟨PStep.refl hck.state, ?_⟩
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
          refine ⟨PStep.refl hck.state, ?_⟩
          show (false : Bool) = _
          simp only [ConLeche.ctorResidualOk, hg', henv, stripPis_none hsq]
          simp
        obtain ⟨sxs, sbodyP, hsps, _, hsbody⟩ := denoteBP_someB hsq
        obtain ⟨fam, s2, k2, hrun3⟩ := bindOk hrun2
        obtain ⟨p2, hfam⟩ :=
          structFam_spec T TP lps lpsP nP nF s₀ s2 fam hck.state ⟨hT, hlps⟩ k2
        obtain ⟨rfl, rfl⟩ := pureOk hrun3
        refine ⟨p2, ?_⟩
        show (sbody == fam) = _
        simp only [ConLeche.ctorResidualOk, hg', henv, hsps]
        rw [beq_ehandle_eq p2.ok.wf (denote_ext hsbody p2.ext) hfam]
        simp
      all_goals
        (rw [hf] at hrun
         obtain ⟨rfl, rfl⟩ := pureOk hrun
         refine ⟨PStep.refl hck.state, ?_⟩
         show (false : Bool) = _
         have hne := denoteCI_not_ctor hci (by simp)
         simp only [ConLeche.ctorResidualOk, hg', henv]
         cases c
         case ctorInfo v n1 n2 => exact absurd rfl (hne v n1 n2)
         all_goals simp)

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
The same at the core grade, read off `ctorResidualOk_run`. -/
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
  obtain ⟨p, hr⟩ := ctorResidualOk_run fe' T ctorName TP ctorNameP lps lpsP nP nF eta
    s₀ s' r hck.toR ⟨hT, hct, hlps⟩ hrun
  exact ⟨p.toCore hck, hr⟩

/-! ## The route's list reads (task #97-P3-Ind round 8)

`checkModeled`'s dispatch reads the block four times by kind (the recursor
suffix, the two partitions, the single former and constructor) and once by
name.  Every one of those is exact on denoting lists: `denoteCI` keeps the
constructor (`denoteCI_kind`) and, off projection tables, the name. -/

/-- con-leche: none — a kind-reading filter commutes with the denotation. -/
theorem denoteCIList_filter {st : EStore} {pA : IConstantInfo → Bool}
    {pC : ConstantInfo → Bool}
    (hp : ∀ ci c, Frontend.denoteCI st ci = some c → pA ci = pC c) :
    ∀ {bs : List IConstantInfo} {bsP : List ConstantInfo},
      Frontend.denoteCIList st bs = some bsP →
      Frontend.denoteCIList st (bs.filter pA) = some (bsP.filter pC)
  | [], bsP, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | ci :: bs, bsP, h => by
    simp only [Frontend.denoteCIList] at h
    cases hc : Frontend.denoteCI st ci with
    | none => rw [hc] at h; simp at h
    | some c =>
    cases hr : Frontend.denoteCIList st bs with
    | none => rw [hc, hr] at h; simp at h
    | some rest =>
    rw [hc, hr] at h
    obtain rfl := (Option.some.inj h).symm
    have ih := denoteCIList_filter hp hr
    by_cases hpc : pA ci = true
    · have hpc' : pC c = true := by rw [← hp ci c hc]; exact hpc
      rw [List.filter_cons_of_pos hpc, List.filter_cons_of_pos hpc']
      simp only [Frontend.denoteCIList, hc, ih]
    · have hpc' : ¬ pC c = true := by rw [← hp ci c hc]; exact hpc
      rw [List.filter_cons_of_neg hpc, List.filter_cons_of_neg hpc']
      exact ih

/-- con-leche: none — the former tag, on both sides. -/
theorem indTag_denote {st : EStore} {ci : IConstantInfo} {c : ConstantInfo} :
    Frontend.denoteCI st ci = some c →
    (match ci with | .indInfo _ _ => true | _ => false) =
      (match c with | .indInfo _ _ => true | _ => false) := by
  intro h
  cases ci
  case axiomInfo v => obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv h; rfl
  case defnInfo v _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv h; rfl
  case thmInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv h; rfl
  case indInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv h; rfl
  case ctorInfo v _ _ => obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv h; rfl
  case recInfo v _ _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv h; rfl
  case projInfo t => obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv h; rfl

/-- con-leche: none — the constructor tag, on both sides. -/
theorem ctorTag_denote {st : EStore} {ci : IConstantInfo} {c : ConstantInfo} :
    Frontend.denoteCI st ci = some c →
    (match ci with | .ctorInfo _ _ _ => true | _ => false) =
      (match c with | .ctorInfo _ _ _ => true | _ => false) := by
  intro h
  cases ci
  case axiomInfo v => obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv h; rfl
  case defnInfo v _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv h; rfl
  case thmInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv h; rfl
  case indInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv h; rfl
  case ctorInfo v _ _ => obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv h; rfl
  case recInfo v _ _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv h; rfl
  case projInfo t => obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv h; rfl

/-- con-leche: none — the recursor tag, on both sides. -/
theorem isRecInfo_denote {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) : Arena.isRecInfo ci = c.isRecInfo := by
  cases ci
  case axiomInfo v => obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv h; rfl
  case defnInfo v _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv h; rfl
  case thmInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv h; rfl
  case indInfo v _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv h; rfl
  case ctorInfo v _ _ => obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv h; rfl
  case recInfo v _ _ _ => obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv h; rfl
  case projInfo t => obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv h; rfl

/-- con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix — the tag pass
is exact on a denoting block. -/
theorem recsFormSuffix_denote {st : EStore} :
    ∀ {bs : List IConstantInfo} {bsP : List ConstantInfo},
      Frontend.denoteCIList st bs = some bsP →
      Arena.recsFormSuffix bs = ConLeche.recsFormSuffix bsP
  | [], bsP, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | ci :: bs, bsP, h => by
    simp only [Frontend.denoteCIList] at h
    cases hc : Frontend.denoteCI st ci with
    | none => rw [hc] at h; simp at h
    | some c =>
    cases hr : Frontend.denoteCIList st bs with
    | none => rw [hc, hr] at h; simp at h
    | some rest =>
    rw [hc, hr] at h
    obtain rfl := (Option.some.inj h).symm
    have hall : ∀ {xs : List IConstantInfo} {xsP : List ConstantInfo},
        Frontend.denoteCIList st xs = some xsP →
        xs.all Arena.isRecInfo = xsP.all ConLeche.ConstantInfo.isRecInfo := by
      intro xs
      induction xs with
      | nil =>
        intro xsP h
        simp only [Frontend.denoteCIList, Option.some.injEq] at h
        subst h; rfl
      | cons x xs ih =>
        intro xsP h
        simp only [Frontend.denoteCIList] at h
        cases hx : Frontend.denoteCI st x with
        | none => rw [hx] at h; simp at h
        | some xc =>
        cases hxs : Frontend.denoteCIList st xs with
        | none => rw [hx, hxs] at h; simp at h
        | some xsP' =>
        rw [hx, hxs] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.all_cons, isRecInfo_denote hx, ih hxs]
    simp only [Arena.recsFormSuffix, ConLeche.recsFormSuffix, isRecInfo_denote hc,
      hall hr, recsFormSuffix_denote hr]

/-- con-leche: ConLeche/Kernel/Env.lean:786-792 blockRecSuffixDec — the
substituted decision IS the tag pass. -/
theorem blockRecSuffixDec_decide (b : List ConstantInfo) :
    @decide _ (ConLeche.blockRecSuffixDec b) = ConLeche.recsFormSuffix b := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact (ConLeche.recsFormSuffix_iff b).symm

/-- con-leche: none — a block of non-table members names what its
denotation names. -/
theorem denoteCIList_names {st : EStore} :
    ∀ {bs : List IConstantInfo} {bsP : List ConstantInfo},
      (∀ ci ∈ bs, ∀ t, ci ≠ .projInfo t) →
      Frontend.denoteCIList st bs = some bsP →
      Frontend.denoteNList st.ns (bs.map (·.name)) = some (bsP.map (·.name))
  | [], bsP, _, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | ci :: bs, bsP, hnp, h => by
    simp only [Frontend.denoteCIList] at h
    cases hc : Frontend.denoteCI st ci with
    | none => rw [hc] at h; simp at h
    | some c =>
    cases hr : Frontend.denoteCIList st bs with
    | none => rw [hc, hr] at h; simp at h
    | some rest =>
    rw [hc, hr] at h
    obtain rfl := (Option.some.inj h).symm
    have hn := denoteCI_name_of (fun t ht => absurd ht (hnp ci (by simp) t)) hc
    have ih := denoteCIList_names (fun x hx => hnp x (by simp [hx])) hr
    simp only [List.map_cons, Frontend.denoteNList, hn, ih]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
(its shape) — **an accepted member is a former or a constructor**: every
other kind reaches the twin's last `fail`.  Structural. -/
theorem checkIndMember_kind {μ : CheckMode} {bn : List NIdx} {caps : IIndCaps}
    {fe : IFEnv} {ci : IConstantInfo} {s s' : AState} {r : IFEnv}
    (h : Arena.checkIndMember μ bn caps fe ci s = .ok (r, s')) : ∀ t, ci ≠ .projInfo t := by
  intro t ht
  subst ht
  simp only [Arena.checkIndMember] at h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨_, _, _, h⟩ := bindOk h
  exact absurd h (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- con-leche: none — and so is every member of an accepted member fold. -/
theorem checkIndMembers_kind {μ : CheckMode} {bn : List NIdx} {caps : IIndCaps} :
    ∀ {cis : List IConstantInfo} {fe : IFEnv} {s s' : AState} {r : IFEnv},
      Arena.checkIndMembers μ bn caps fe cis s = .ok (r, s') →
      ∀ ci ∈ cis, ∀ t, ci ≠ .projInfo t
  | [], _, _, _, _, _ => by simp
  | ci :: cis, fe, s, s', r, h => by
    simp only [Arena.checkIndMembers] at h
    obtain ⟨fe₁, s₁, k1, z1⟩ := bindOk h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact checkIndMember_kind k1
    · exact checkIndMembers_kind z1 x hx

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:459 checkIndRecsS_run (its
`EnvWF` half) — **the recursor group leaves a well-formed environment**, V-free.
Part of the same ask. -/
theorem checkIndRecs_envWF {μ : CheckMode} {F : Nat} {bn : List ConLeche.Name}
    {env₂ e : Env} {recs : List ConstantInfo} (henv : EnvWF env₂)
    (hbn : ∀ ci ∈ recs, bn.contains ci.name = true)
    (h : ConLeche.checkIndRecs μ (ConLeche.fueledOps μ F) bn env₂ recs = .ok e) :
    EnvWF e := by
  sorry

/-- con-leche: none — a one-element block list denotes one constant. -/
theorem denoteCIList_single {st : EStore} {ci : IConstantInfo} {L : List ConstantInfo}
    (h : Frontend.denoteCIList st [ci] = some L) :
    ∃ c, Frontend.denoteCI st ci = some c ∧ L = [c] := by
  simp only [Frontend.denoteCIList] at h
  cases hc : Frontend.denoteCI st ci with
  | none => rw [hc] at h; simp at h
  | some c =>
    rw [hc] at h
    exact ⟨c, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — a block list denoting a one-element list is one
constant. -/
theorem denoteCIList_single_inv {st : EStore} {L : List IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCIList st L = some [c]) :
    ∃ x, Frontend.denoteCI st x = some c ∧ L = [x] := by
  match L, h with
  | [], h => simp [Frontend.denoteCIList] at h
  | x :: xs, h =>
    simp only [Frontend.denoteCIList] at h
    cases hx : Frontend.denoteCI st x with
    | none => rw [hx] at h; simp at h
    | some c' =>
    cases hxs : Frontend.denoteCIList st xs with
    | none => rw [hx, hxs] at h; simp at h
    | some rest =>
    rw [hx, hxs] at h
    simp only [Option.some.injEq, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match xs, hxs with
    | [], _ => exact ⟨x, hx, rfl⟩
    | y :: ys, hxs =>
      simp only [Frontend.denoteCIList] at hxs
      split at hxs <;> simp at hxs

/-- con-leche: none — a constant denoting a former is a former. -/
theorem denoteCI_ind_of {st : EStore} {x : IConstantInfo} {cv : ConstantVal} {d : IndCaps}
    (h : Frontend.denoteCI st x = some (.indInfo cv d)) : ∃ v c, x = .indInfo v c := by
  have hk := denoteCI_kind h
  cases x <;> simp_all [iciKind, ciKind]

/-- con-leche: none — a constant denoting a constructor is a constructor. -/
theorem denoteCI_ctor_of {st : EStore} {x : IConstantInfo} {cv : ConstantVal} {a b : Nat}
    (h : Frontend.denoteCI st x = some (.ctorInfo cv a b)) :
    ∃ v a' b', x = .ctorInfo v a' b' := by
  have hk := denoteCI_kind h
  cases x <;> simp_all [iciKind, ciKind]

/-- con-leche: none — the capability record's `eta` bit is copied. -/
theorem denoteCaps_eta {st : EStore} {c : IIndCaps} {d : IndCaps}
    (h : Frontend.denoteCaps st c = some d) : c.eta = d.eta := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · obtain rfl := (Option.some.inj h); rfl
  · exact nomatch h

/-- con-leche: none — the empty capability record denotes the empty one, once
the pin phase has run (`PinsOK.anon`). -/
theorem denoteCaps_empty {s : AState} (hp : PinsOK s) :
    Frontend.denoteCaps s.store ({} : IIndCaps) = some ({} : IndCaps) := by
  simp only [Frontend.denoteCaps]
  have : denoteN s.store.ns ({} : IIndCaps).etaCtor = some ConLeche.Name.anonymous := hp.anon
  rw [this]

/-- con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
**THE MODELED ROUTE**, the second of `checkIndDecl`'s two dispatches: every
member checked against its `_model` counterpart, the recursors installed as a
group, and — at a structure-like block — the projection functions.

`sorry`: `indBlockCaps_spec`, `checkIndMembers_spec`, `checkIndRecs_spec`,
`ctorResidualOk_spec`, `ctorTargetsFam_spec`, `installProjFns_spec`, and
`recsFormSuffix`/`isRecInfo`'s exactness (both tag reads, so both are
`Frontend.denoteCI`'s case split). -/
theorem checkModeled_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    ISpec
      (fun s => CheckOK μ env fe s ∧ Frontend.denoteCIList s.store block = some blockP ∧
        denoteFEnv s.store fe = some env ∧ IFEnvCoh fe)
      (Arena.checkModeled μ fe block)
      (fun s fe' => InstRel fe (fun e => ∃ F, ConLeche.checkModeled μ
        (ConLeche.fueledOps μ F) env blockP = .ok e) s.store fe') := by
  intro s₀ s' r hpre hrun
  obtain ⟨hck, hb, hfe, hcoh⟩ := hpre
  have hwf := hck.state.wf
  simp only [Arena.checkModeled] at hrun
  -- the recursor suffix
  obtain ⟨hsuf, z1⟩ := AM.dunless_ok AM.Never.fail_any hrun
  replace z1 := AM.pure_bind_ok z1
  have hsufP : ConLeche.recsFormSuffix blockP = true := by
    rw [← recsFormSuffix_denote hb]; exact hsuf
  -- the two partitions, denoted
  have hrecs := denoteCIList_filter (pA := Arena.isRecInfo)
    (pC := fun ci => match ci with | .recInfo _ _ _ _ => true | _ => false)
    (fun ci c h => by rw [isRecInfo_denote h]; cases c <;> rfl) hb
  have hnon := denoteCIList_filter (pA := fun ci => !Arena.isRecInfo ci)
    (pC := fun ci => match ci with | .recInfo _ _ _ _ => false | _ => true)
    (fun ci c h => by rw [isRecInfo_denote h]; cases c <;> rfl) hb
  have hinds := denoteCIList_filter
    (pA := fun ci => match ci with | .indInfo _ _ => true | _ => false)
    (pC := fun ci => match ci with | .indInfo _ _ => true | _ => false)
    (fun ci c h => indTag_denote h) hb
  have hctors := denoteCIList_filter
    (pA := fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false)
    (pC := fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false)
    (fun ci c h => ctorTag_denote h) hb
  generalize hI : List.filter (fun ci => match ci with | .indInfo _ _ => true | _ => false)
    block = LI at z1 hinds
  generalize hC : List.filter (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false)
    block = LC at z1 hctors
  by_cases hshape : ∃ cvT c0 cvC nP nF, LI = [.indInfo cvT c0] ∧ LC = [.ctorInfo cvC nP nF]
  · obtain ⟨cvT, c0, cvC, nP, nF, rfl, rfl⟩ := hshape
    dsimp only at z1
    obtain ⟨cI, hcI, hIP⟩ := denoteCIList_single hinds
    obtain ⟨cvTP, c0P, rfl, hcvT, -⟩ := denoteCI_ind_inv hcI
    obtain ⟨cC, hcC, hCP⟩ := denoteCIList_single hctors
    obtain ⟨cvCP, rfl, hcvC⟩ := denoteCI_ctor_inv hcC
    -- the capability record, at the entry index
    obtain ⟨caps, s₁, k1, z2⟩ := bindOk z1
    obtain ⟨c1, hcaps⟩ := indBlockCaps_spec fe cvT cvC cvTP cvCP nP nF s₀ s₁ caps hck
      ⟨hcvT, hcvC, hfe⟩ k1
    -- the members
    obtain ⟨fe₂, s₂, k2, z3⟩ := bindOk z2
    have hnpB : ∀ ci ∈ block, ∀ t, ci ≠ .projInfo t := by
      intro ci hci t ht
      subst ht
      exact checkIndMembers_kind k2 _ (List.mem_filter.mpr ⟨hci, rfl⟩) t rfl
    have hbn := denoteCIList_names hnpB hb
    have hpins : ∀ ci ∈ blockP.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true), ∀ cv caps₀, ci = .indInfo cv caps₀ →
        ConLeche.EtaPins μ env cv.name cv.levelParams
          (ConLeche.indBlockCaps μ env cvTP cvCP nP nF) := by
      intro ci hci cv caps₀ hceq
      have hmemI : ci ∈ blockP.filter (fun ci => match ci with
          | .indInfo _ _ => true | _ => false) :=
        List.mem_filter.mpr ⟨(List.mem_filter.mp hci).1, by subst hceq; rfl⟩
      rw [hIP] at hmemI
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (hceq ▸ List.mem_singleton.mp hmemI)
      exact ConLeche.etaPins_of_indBlockCaps
    have x1 := c1.ext
    obtain ⟨i2, hinst₂⟩ := checkIndMembers_spec fe hμ hk henv hcoh (block.map (·.name))
      (blockP.map (·.name)) caps _ _ _ hpins s₁ s₂ fe₂
      ⟨c1.ok.toR, denoteNListE_ext x1 _ _ hbn, hcaps, denoteCIList_ext x1 _ _ hnon,
        denoteFEnv_ext x1 hfe⟩ k2
    obtain ⟨env₂, hden₂, ⟨F₁, hF₁⟩, hread₂⟩ := hinst₂.denote
    have henv₂ := foldIndMember_envWF henv hpins hF₁
    have x2 : Ext s₀.store s₂.store := x1.trans i2.ext
    -- the recursors
    obtain ⟨fe₃, s₃, k3, z4⟩ := bindOk z3
    obtain ⟨i3, hinst₃⟩ := checkIndRecs_spec fe₂ hμ hk henv₂ hinst₂.coh (block.map (·.name))
      (blockP.map (·.name)) _ _ s₂ s₃ fe₃
      ⟨hread₂, denoteNListE_ext x2 _ _ hbn, denoteCIList_ext x2 _ _ hrecs, hden₂⟩ k3
    obtain ⟨env₃, hden₃, ⟨F₂, hF₂⟩, hread₃⟩ := hinst₃.denote
    have hbnR : ∀ ci ∈ blockP.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
        (blockP.map (·.name)).contains ci.name = true := by
      intro ci hci
      have : ci.name ∈ blockP.map (·.name) :=
        List.mem_map_of_mem (List.mem_filter.mp hci).1
      simpa using this
    have henv₃ := checkIndRecs_envWF henv₂ hbnR hF₂
    have x3 : Ext s₀.store s₃.store := x2.trans i3.ext
    have hT3 := denoteN_ext (denoteCV_name hcvT) x3
    have hC3 := denoteN_ext (denoteCV_name hcvC) x3
    have hL3 := denoteNListE_ext x3 _ _ (denoteCV_lps hcvT)
    -- the eta capability's constructor
    obtain ⟨b4, s₄, k4, z5⟩ := bindOk z4
    obtain ⟨p4, hb4⟩ := ctorResidualOk_run fe₃ cvT.name cvC.name cvTP.name cvCP.name
      cvT.levelParams cvTP.levelParams nP nF caps.eta s₃ s₄ b4 hread₃ ⟨hT3, hC3, hL3⟩ k4
    obtain ⟨hb4', z6⟩ := AM.dunless_ok AM.Never.fail_any z5
    replace z6 := AM.pure_bind_ok z6
    rw [hb4, denoteCaps_eta hcaps] at hb4'
    -- the projection name family
    have hread₄ : ReadOK env₃ fe₃ s₄ := hread₃.mono p4.ok p4.ext p4.pins
    obtain ⟨b5, s₅, k5, z7⟩ := bindOk z6
    obtain ⟨p5, hb5⟩ := allM_ck (env := env₃) (fe := fe₃)
      (g := fun j => (env₃.find? (ConLeche.projFnName cvTP.name j)).isNone)
      (fun _ st => denoteN st.ns cvT.name = some cvTP.name) (fun hx h => denoteN_ext h hx)
      (fun j t t' b hok hP hrun => by
        obtain ⟨h, t1, g1, y1⟩ := bindOk hrun
        obtain ⟨q1, hh⟩ := projFnName_run hok.state hP g1
        obtain ⟨rfl, rfl⟩ := pureOk y1
        refine ⟨q1, ?_⟩
        have e := (hok.mono q1.ok q1.ext q1.pins).ienv.find_isSome q1.ok hh
        revert e
        cases fe₃.find? h <;> cases env₃.find? (ConLeche.projFnName cvTP.name j) <;> simp)
      (List.range nF) s₄ s₅ b5 hread₄ (fun _ _ => denoteN_ext hT3 p4.ext) k5
    obtain ⟨hb5', z8⟩ := AM.dunless_ok AM.Never.fail_any z7
    replace z8 := AM.pure_bind_ok z8
    rw [hb5] at hb5'
    -- the projection functions, at a structure-like block
    have x5 : Ext s₃.store s₅.store := p4.ext.trans p5.ext
    obtain ⟨b6, s₆, k6, z9⟩ := bindOk z8
    obtain ⟨p6, hb6⟩ := ctorTargetsFam_spec cvC.type cvCP.type cvT.name cvTP.name
      cvT.levelParams cvTP.levelParams nP nF s₅ s₆ b6 p5.ok
      ⟨denote_ext (denoteCV_type hcvC) (x3.trans x5), denoteN_ext hT3 x5,
        denoteNListE_ext x5 _ _ hL3⟩ k6
    have x6 : Ext s₃.store s₆.store := x5.trans p6.ext
    have i36 : InstStep s₃ s₆ := (p4.toInst.trans p5.toInst).trans p6.toInst
    have i06 : InstStep s₀ s₆ := (c1.toInst.trans (i2.trans i3)).trans i36
    have htail : InstStep s₃ s' ∧ InstRel fe₃ (fun e => ∃ F,
        (if ConLeche.ctorTargetsFam cvCP.type cvTP.name cvTP.levelParams nP nF = true then
          (List.range nF).foldlM (ConLeche.installProjFnStep μ (ConLeche.fueledOps μ F)
            cvTP.name cvCP.name cvTP.levelParams nP nF) env₃
        else (pure env₃ : Except ConLeche.CheckError Env)) = .ok e) s'.store r := by
      cases b6
      · simp only [Bool.false_eq_true, if_false] at z9
        obtain ⟨rfl, rfl⟩ := pureOk z9
        refine ⟨i36, hinst₃.coh, Pushed.refl _, Nat.le_refl _,
          ⟨env₃, denoteFEnv_ext x6 hden₃, 0, ?_⟩, ProjOut.refl _ _⟩
        rw [← hb6]
        rfl
      · simp only [if_true] at z9
        obtain ⟨i7, hinst₇⟩ := installProjFns_spec fe₃ hk henv₃ hinst₃.coh cvT.name cvC.name
          cvTP.name cvCP.name cvT.levelParams cvTP.levelParams nP nF nF 0 s₆ s' r
          ⟨hread₃.ofInst i36, denoteN_ext hT3 x6, denoteN_ext hC3 x6,
            denoteNListE_ext x6 _ _ hL3, denoteFEnv_ext x6 hden₃⟩ z9
        refine ⟨i36.trans i7, hinst₇.imp ?_⟩
        rintro e ⟨⟨F, hF⟩, -⟩
        refine ⟨F, ?_⟩
        rw [← hb6]
        simp only [if_true, Nat.zero_add] at hF ⊢
        exact hF
    refine ⟨(c1.toInst.trans (i2.trans i3)).trans htail.1, ?_⟩
    have hall := InstRel.trans (i3.ext.trans htail.1.ext) hinst₂
      (InstRel.trans htail.1.ext hinst₃ htail.2)
    refine hall.imp ?_
    rintro e ⟨F₃, hF₃⟩
    refine ⟨max F₁ (max F₂ F₃), ?_⟩
    have g₁ := foldIndMember_up (show F₁ ≤ max F₁ (max F₂ F₃) by omega) hF₁
    have g₂ := checkIndRecs_up (show F₂ ≤ max F₁ (max F₂ F₃) by omega) hF₂
    simp only [ConLeche.checkModeled]
    rw [if_pos (by rw [blockRecSuffixDec_decide]; exact hsufP)]
    erw [hIP, hCP]
    dsimp only
    simp only [bind, Except.bind, pure, Except.pure]
    erw [g₁]
    dsimp only
    erw [g₂]
    dsimp only
    rw [if_pos hb4', if_pos hb5']
    by_cases hct : ConLeche.ctorTargetsFam cvCP.type cvTP.name cvTP.levelParams nP nF = true
    · rw [if_pos hct] at hF₃ ⊢
      exact foldProjFn_up (show F₃ ≤ max F₁ (max F₂ F₃) by omega) hF₃
    · rw [if_neg hct] at hF₃ ⊢
      exact hF₃
  · -- any other block: the members with the empty record, then the recursors
    have z1' : (do
        let fe₂ ← Arena.checkIndMembers μ (block.map (·.name)) {} fe
          (block.filter (fun ci => !Arena.isRecInfo ci))
        Arena.checkIndRecs μ (block.map (·.name)) fe₂ (block.filter Arena.isRecInfo)
        : AM IFEnv) s₀ = .ok (r, s') := by
      rcases LI with _ | ⟨x, _ | ⟨y, L⟩⟩ <;> rcases LC with _ | ⟨u, _ | ⟨v, M⟩⟩ <;>
        (try cases x) <;> (try cases u) <;>
        first | exact z1 | exact absurd ⟨_, _, _, _, _, rfl, rfl⟩ hshape
    obtain ⟨fe₂, s₂, k2, z3⟩ := bindOk z1'
    have hnpB : ∀ ci ∈ block, ∀ t, ci ≠ .projInfo t := by
      intro ci hci t ht
      subst ht
      exact checkIndMembers_kind k2 _ (List.mem_filter.mpr ⟨hci, rfl⟩) t rfl
    have hbn := denoteCIList_names hnpB hb
    have hpins : ∀ ci ∈ blockP.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true), ∀ cv caps₀, ci = .indInfo cv caps₀ →
        ConLeche.EtaPins μ env cv.name cv.levelParams ({} : IndCaps) :=
      fun _ _ _ _ _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    obtain ⟨i2, hinst₂⟩ := checkIndMembers_spec fe hμ hk henv hcoh (block.map (·.name))
      (blockP.map (·.name)) {} {} _ _ hpins s₀ s₂ fe₂
      ⟨hck.toR, hbn, denoteCaps_empty hck.pins, hnon, hfe⟩ k2
    obtain ⟨env₂, hden₂, ⟨F₁, hF₁⟩, hread₂⟩ := hinst₂.denote
    have henv₂ := foldIndMember_envWF henv hpins hF₁
    have x2 : Ext s₀.store s₂.store := i2.ext
    obtain ⟨i3, hinst₃⟩ := checkIndRecs_spec fe₂ hμ hk henv₂ hinst₂.coh (block.map (·.name))
      (blockP.map (·.name)) _ _ s₂ s' r
      ⟨hread₂, denoteNListE_ext x2 _ _ hbn, denoteCIList_ext x2 _ _ hrecs, hden₂⟩ z3
    refine ⟨i2.trans i3, ?_⟩
    have hall := InstRel.trans i3.ext hinst₂ hinst₃
    refine hall.imp ?_
    rintro e ⟨⟨F₂, hF₂⟩, -⟩
    refine ⟨max F₁ F₂, ?_⟩
    have g₁ := foldIndMember_up (Nat.le_max_left F₁ F₂) hF₁
    have g₂ := checkIndRecs_up (Nat.le_max_right F₁ F₂) hF₂
    simp only [ConLeche.checkModeled]
    rw [if_pos (by rw [blockRecSuffixDec_decide]; exact hsufP)]
    split
    · rename_i cvT c0 cvC nP nF heqI heqC
      exfalso
      erw [heqI] at hinds
      erw [heqC] at hctors
      obtain ⟨xI, hxI, hLI⟩ := denoteCIList_single_inv hinds
      obtain ⟨xC, hxC, hLC⟩ := denoteCIList_single_inv hctors
      obtain ⟨v1, c1, rfl⟩ := denoteCI_ind_of hxI
      obtain ⟨v2, a2, b2, rfl⟩ := denoteCI_ctor_of hxC
      exact hshape ⟨v1, c1, v2, a2, b2, hLI, hLC⟩
    · simp only [bind, Except.bind]
      erw [g₁]
      exact g₂

end ConRon.Bridge.Inductives

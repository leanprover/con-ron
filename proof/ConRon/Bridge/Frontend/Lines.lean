/-
# `ConRon.Bridge.Frontend.Lines` — one scanned line, applied

The scanner is **reused, not twinned** (`Arena/Frontend/ExportC.lean` imports
`ConLeche.Frontend.Scan.Fast` and calls `scanLineFwd`), so a line's `LineRec`
is con-leche's own value on both sides and there is nothing to relate about
it.  What this module states is the SEMANTIC layer: what the twin does with
that record, against what con-leche does with the same record.

Every theorem has one shape, and it is the shape the monad seam forces
(`Bridge/Frontend/Rel.lean`'s module note): **the twin succeeding implies
con-leche succeeding**, with the twin's answer denoting con-leche's, plus the
store frame.  A twin `fail` claims nothing.

    theorem f_run (hok : StateOK s) (hoff : s.store.scratchOn = false)
        (hrel : StateDRel s.store sd sc) (hp : PersStateD sd)
        (hrun : Arena.Frontend.f … sd … s = .ok (x, s')) :
      StateOK s' ∧ Ext s.store s'.store ∧ s'.store.scratchOn = false ∧
        s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
        ∃ y, ConLeche.Frontend.f … sc … = .ok y ∧ …Rel s'.store x y

The five frame conjuncts are what every caller needs and what nothing in the
frontend breaks: **the parse interns and does nothing else.**  It never
enters the scratch tier (`Arena/Main.lean` runs `internReservedPins` first and
the fold's bracket has not started), never writes a per-declaration cache and
never touches the pin table — which is what makes `PersStateD` free and what
makes `Bridge/Checker/Capstone.lean`'s `FoldOK` reachable at the post-parse
state.
-/
import ConRon.Bridge.Frontend.Modeller
import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.Frontend.ProjRec

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The verdict, and the sum -/

/-- con-leche: ConLeche/Frontend/Export.lean:77-81 RecordVerdict — two record
verdicts agree in KIND.  The twin's verdict STRINGS are con-leche's wherever
the string is a literal, and are not where it names a block (a handle renders
differently from a `Name`), so the relation is the constructor and not the
text: what every consumer reads is `RecordVerdict.toError`'s KIND, hence the
exit code, and `Arena/Frontend/Types.lean`'s own note says the same. -/
def VerdictRel : RecordVerdict → ConLeche.Frontend.RecordVerdict → Prop
  | .declined _, .declined _ => True
  | .invalid _, .invalid _ => True
  | _, _ => False

/-- con-leche: ConLeche/Frontend/ExportC.lean:629 processLineCoreD — the
`StateD ⊕ RecordVerdict` the record's semantics returns, related. -/
def SumRel (st : EStore) : StateD ⊕ RecordVerdict →
    ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict → Prop
  | .inl sd, .inl sc => StateDRel st sd sc
  | .inr v, .inr w => VerdictRel v w
  | _, _ => False

/-- con-leche: none — **the one direction the capstone consumes**: a line the
twin APPLIES is a line con-leche applies, with the two states related.  A
verdict on the twin's side is a verdict on con-leche's and the chunk driver
errors on both, which is why the chunk theorems need nothing else about the
`.inr` arm. -/
theorem SumRel.inl_left {st : EStore} {x : StateD ⊕ RecordVerdict}
    {y : ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict}
    (h : SumRel st x y) {sd : StateD} (hx : x = .inl sd) :
    ∃ sc, y = .inl sc ∧ StateDRel st sd sc := by
  cases y with
  | inl sc => subst hx; exact ⟨sc, rfl, h⟩
  | inr w => subst hx; exact absurd h (by simp [SumRel])

/-- con-leche: none — the mirror at the verdict arm. -/
theorem SumRel.inr_left {st : EStore} {x : StateD ⊕ RecordVerdict}
    {y : ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict}
    (h : SumRel st x y) {v : RecordVerdict} (hx : x = .inr v) :
    ∃ w, y = .inr w ∧ VerdictRel v w := by
  cases y with
  | inl sc => subst hx; exact absurd h (by simp [SumRel])
  | inr w => subst hx; exact ⟨w, rfl, h⟩

/-- con-leche: none — the `SumRel` of two related states, which is what every
`.inl` arm of `processLineCoreD` produces. -/
theorem SumRel.of_state {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    SumRel st (.inl sd) (.inl sc) := h

/-! ## The three table reads

`StateD.name` / `.level` / `.expr` are `IdTableRel` read off, and they are the
tier's smallest theorems: one `OptRel.some_left`. -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:164-167 StateD.name. -/
theorem StateD_name_run {s s' : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) {i : Nat}
    {h : NIdx} (hrun : sd.name i s = .ok (h, s')) :
    s' = s ∧ ∃ n, ConLeche.Frontend.StateD.name sc i = .ok n ∧
      denoteN s.store.ns h = some n := by
  simp only [ConRon.Arena.Frontend.StateD.name] at hrun
  cases hg : sd.names.get? i with
  | none =>
    rw [hg] at hrun
    exact nomatch hrun
  | some h' =>
    rw [hg] at hrun
    obtain ⟨n, hn, hd⟩ := (hrel.names i).some_left hg
    injection hrun with e1
    injection e1 with e2 e3
    subst e2; subst e3
    refine ⟨rfl, n, ?_, hd⟩
    simp only [ConLeche.Frontend.StateD.name, hn]
    rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:169-172 StateD.level. -/
theorem StateD_level_run {s s' : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) {i : Nat}
    {l : LIdx} (hrun : sd.level i s = .ok (l, s')) :
    s' = s ∧ ∃ u, ConLeche.Frontend.StateD.level sc i = .ok u ∧
      denoteL s.store.ls l = some u := by
  simp only [ConRon.Arena.Frontend.StateD.level] at hrun
  cases hg : sd.levels.get? i with
  | none =>
    rw [hg] at hrun
    exact nomatch hrun
  | some h' =>
    rw [hg] at hrun
    obtain ⟨u, hn, hd⟩ := (hrel.levels i).some_left hg
    injection hrun with e1
    injection e1 with e2 e3
    subst e2; subst e3
    refine ⟨rfl, u, ?_, hd⟩
    simp only [ConLeche.Frontend.StateD.level, hn]
    rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:174-177 StateD.expr. -/
theorem StateD_expr_run {s s' : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) {i : Nat}
    {h : EIdx} (hrun : sd.expr i s = .ok (h, s')) :
    s' = s ∧ ∃ e, ConLeche.Frontend.StateD.expr sc i = .ok e ∧
      denoteE s.store h = some e := by
  simp only [ConRon.Arena.Frontend.StateD.expr] at hrun
  cases hg : sd.exprs.get? i with
  | none =>
    rw [hg] at hrun
    exact nomatch hrun
  | some h' =>
    rw [hg] at hrun
    obtain ⟨e, hn, hd⟩ := (hrel.exprs i).some_left hg
    injection hrun with e1
    injection e1 with e2 e3
    subst e2; subst e3
    refine ⟨rfl, e, ?_, hd⟩
    simp only [ConLeche.Frontend.StateD.expr, hn]
    rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:188 getDeclD — the
declaration-level expression lookup is `StateD.expr` on both sides. -/
theorem getDeclD_run {s s' : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) {i : Nat}
    {h : EIdx} (hrun : getDeclD sd i s = .ok (h, s')) :
    s' = s ∧ ∃ e, ConLeche.Frontend.getDeclD sc i = .ok e ∧
      denoteE s.store h = some e :=
  StateD_expr_run hrel hrun

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `readName` as a run.
`Bridge/Specs.lean` states it as a Hoare triple (it is `mvcgen`'s vocabulary);
`Bridge/Rel.lean`'s `AM.of_run` is the four-line bridge back to the shape
every theorem of this tier is stated in. -/
theorem readName_run {s s' : AState} {h : NIdx} {x : ConLeche.Name}
    (hrun : readName h s = .ok (x, s')) :
    s' = s ∧ denoteN s.store.ns h = some x :=
  AM.of_run (P := fun t => t = s) rfl hrun (readName_spec s h)

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the readback at a LIST
of handles, which is what `parsePwD` runs: `PropWhen` holds `ConLeche.Name`s,
so the resolved handles are read BACK, and the readback IS `denoteN`. -/
theorem readNames_mapM_run {s : AState} :
    ∀ (hs : List NIdx) {xs : List ConLeche.Name} {s' : AState},
      (hs.mapM readName) s = .ok (xs, s') →
        s' = s ∧ denoteNList s.store.ns hs = some xs := by
  intro hs
  induction hs with
  | nil =>
    intro xs s' hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨rfl, rfl⟩
  | cons h hs ih =>
    intro xs s' hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s₁, hone, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hdx⟩ := readName_run hone
    subst hs1
    obtain ⟨ys, s₂, hmany, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs2, hdys⟩ := ih hmany
    subst hs2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hv; subst hst
    exact ⟨rfl, by simp only [denoteNList, hdx, hdys]⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:164-167 StateD.name — the name
table read at a LIST of stream indices: `parseCVD`'s level-parameter list and
`parsePwD`'s `ifAllZero` one.  `List.mapM_cons` at `AM` on one side and at
`Except String` on the other; neither side moves anything. -/
theorem StateD_names_run {s : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) :
    ∀ (is : List Nat) {hs : List NIdx} {s' : AState},
      (is.mapM sd.name) s = .ok (hs, s') →
        s' = s ∧ ∃ xs, is.mapM (ConLeche.Frontend.StateD.name sc) = .ok xs ∧
          denoteNList s.store.ns hs = some xs := by
  intro is
  induction is with
  | nil =>
    intro hs s' hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨rfl, [], rfl, rfl⟩
  | cons i is ih =>
    intro hs s' hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨h, s₁, hone, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, n, hcln, hdn⟩ := StateD_name_run hrel hone
    subst hs1
    obtain ⟨hs', s₂, hmany, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs2, xs, hclxs, hdxs⟩ := ih hmany
    subst hs2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hv; subst hst
    refine ⟨rfl, n :: xs, ?_, by simp only [denoteNList, hdn, hdxs]⟩
    simp only [List.mapM_cons, hcln, hclxs]
    rfl

/-! ## The three rebinding guards

Each is `if table.bound i then fail else pure ()`, so a successful run is the
guard's own answer — and `IdTableRel.bound` makes con-leche's guard answer the
same thing at the same index. -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:211-220 StateD.freshName. -/
theorem freshName_run {s s' : AState} {sd : StateD} {i : Nat} {u : Unit}
    (hrun : sd.freshName i s = .ok (u, s')) :
    s' = s ∧ sd.names.bound i = false := by
  rw [ConRon.Arena.Frontend.StateD.freshName] at hrun
  by_cases hb : sd.names.bound i = true
  · rw [if_pos hb] at hrun; exact absurd (AM.fail_ok hrun) (by simp)
  · rw [if_neg hb] at hrun
    exact ⟨(AM.pure_ok hrun).2, by simpa using hb⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:221-222 StateD.freshLevel. -/
theorem freshLevel_run {s s' : AState} {sd : StateD} {i : Nat} {u : Unit}
    (hrun : sd.freshLevel i s = .ok (u, s')) :
    s' = s ∧ sd.levels.bound i = false := by
  rw [ConRon.Arena.Frontend.StateD.freshLevel] at hrun
  by_cases hb : sd.levels.bound i = true
  · rw [if_pos hb] at hrun; exact absurd (AM.fail_ok hrun) (by simp)
  · rw [if_neg hb] at hrun
    exact ⟨(AM.pure_ok hrun).2, by simpa using hb⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:223-224 StateD.freshExpr. -/
theorem freshExpr_run {s s' : AState} {sd : StateD} {i : Nat} {u : Unit}
    (hrun : sd.freshExpr i s = .ok (u, s')) :
    s' = s ∧ sd.exprs.bound i = false := by
  rw [ConRon.Arena.Frontend.StateD.freshExpr] at hrun
  by_cases hb : sd.exprs.bound i = true
  · rw [if_pos hb] at hrun; exact absurd (AM.fail_ok hrun) (by simp)
  · rw [if_neg hb] at hrun
    exact ⟨(AM.pure_ok hrun).2, by simpa using hb⟩

/-! ## The three table writes

`PersStateD` at an inserted index, once per table: the new handle is the
intern's (persistent because the scratch tier is closed), and every other
index is the old table's. -/

theorem PersStateD.insertName {sd : StateD} (hp : PersStateD sd) {i : Nat}
    {h : NIdx} (hh : PersN h) :
    PersStateD { sd with names := sd.names.insert i h } where
  names := by
    intro j x hx
    rw [ConLeche.Frontend.IdTable.get?_insert] at hx
    split at hx
    · rw [← Option.some.inj hx]; exact hh
    · exact hp.names j x hx
  levels := hp.levels
  exprs := hp.exprs
  decls := hp.decls

theorem PersStateD.insertLevel {sd : StateD} (hp : PersStateD sd) {i : Nat}
    {l : LIdx} (hl : PersL l) :
    PersStateD { sd with levels := sd.levels.insert i l } where
  names := hp.names
  levels := by
    intro j x hx
    rw [ConLeche.Frontend.IdTable.get?_insert] at hx
    split at hx
    · rw [← Option.some.inj hx]; exact hl
    · exact hp.levels j x hx
  exprs := hp.exprs
  decls := hp.decls

theorem PersStateD.insertExpr {sd : StateD} (hp : PersStateD sd) {i : Nat}
    {e : EIdx} (he : PersE e) :
    PersStateD { sd with exprs := sd.exprs.insert i e } where
  names := hp.names
  levels := hp.levels
  exprs := by
    intro j x hx
    rw [ConLeche.Frontend.IdTable.get?_insert] at hx
    split at hx
    · rw [← Option.some.inj hx]; exact he
    · exact hp.exprs j x hx
  decls := hp.decls

/-- con-leche: none — every handle of a level-handle list that denotes,
denotes: `internLsNode`'s `ViewOK` at the `const` arm. -/
theorem denoteLList_mem {st : LStore} :
    ∀ {vs : List LIdx} {xs : List Level}, denoteLList st vs = some xs →
      ∀ c ∈ vs, ∃ u, denoteL st c = some u := by
  intro vs
  induction vs with
  | nil => intro xs h c hc; exact absurd hc (by simp)
  | cons a as ih =>
    intro xs h c hc
    rw [denoteLList, opt2_eq_some_iff] at h
    obtain ⟨u, us, hu, hus, -⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨u, hu⟩
    · exact ih hus c hc'

/-- con-leche: ConLeche/Frontend/ExportC.lean:169-172 StateD.level — the level
table read at a LIST of stream indices: `parseExprEntryD`'s `const` arm.  The
`StateD_names_run` shape at the level table. -/
theorem StateD_levels_run {s : AState} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) :
    ∀ (is : List Nat) {hs : List LIdx} {s' : AState},
      (is.mapM sd.level) s = .ok (hs, s') →
        s' = s ∧ ∃ us, is.mapM (ConLeche.Frontend.StateD.level sc) = .ok us ∧
          denoteLList s.store.ls hs = some us := by
  intro is
  induction is with
  | nil =>
    intro hs s' hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨rfl, [], rfl, rfl⟩
  | cons i is ih =>
    intro hs s' hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨l, s₁, hone, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, u, hclu, hdu⟩ := StateD_level_run hrel hone
    rw [hs1] at hrest
    obtain ⟨ls, s₂, hmany, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs2, us, hclus, hdus⟩ := ih hmany
    rw [hs2] at hrest2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hv; subst hst
    refine ⟨rfl, u :: us, ?_, ?_⟩
    · simp only [List.mapM_cons, hclu, hclus]
      rfl
    · simp only [denoteLList, opt2_eq_some_iff]
      exact ⟨u, us, hdu, hdus, rfl⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:192-194 parsePwD — the `pw`
datum.  The twin resolves the handles and READS THEM BACK (`PropWhen` holds
`ConLeche.Name`s, which the binder node carries as values), so the answer is
literally con-leche's and the theorem is an equation, not a relation.

`StateD_names_run` at the list, then `readNames_mapM_run` — `readName`'s
exactness (`Bridge/Specs.lean`) lifted over the list.  The two readbacks of a
handle are the same `denoteN`, which is why the answer is an equation. -/
theorem parsePwD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {r : ConLeche.Frontend.PwRec} {pw : PropWhen}
    (hrun : parsePwD sd r s = .ok (pw, s')) :
    s' = s ∧ ConLeche.Frontend.parsePwD sc r = .ok pw := by
  cases r with
  | never =>
    rw [parsePwD] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨rfl, rfl⟩
  | ifAllZero ns =>
    rw [parsePwD] at hrun
    obtain ⟨hs0, s₁, hnames, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, xs, hcl, hd⟩ := StateD_names_run hrel ns hnames
    subst hs1
    obtain ⟨xs', s₂, hread, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs2, hd2⟩ := readNames_mapM_run hs0 hread
    subst hs2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    obtain rfl : xs' = xs := by
      rw [hd] at hd2; exact (Option.some.injEq _ _ ▸ hd2).symm
    subst hv
    refine ⟨rfl, ?_⟩
    rw [ConLeche.Frontend.parsePwD]
    simp only [hcl]
    rfl

/-! ## The three entry parsers -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:229 parseNameEntryD — a name
entry: the rebinding guard (`IdTableRel.bound` makes it fire on the same
indices), the parent read, the intern, the table insert.

Two arms, and they are the same four moves: `StateD_name_run` at the parent,
`freshName_run` and `IdTableRel.bound` for the guard, `internNNode_istep`
(`Bridge/Frontend/Shared.lean`) for the node, and `IdTableRel.insert` for the
write — the whole of the rest of the relation moving across the append by
`StateDRel.ext`. -/
theorem parseNameEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.NameRec}
    (hrun : parseNameEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseNameEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  cases r with
  | str pre str =>
    rw [ConRon.Arena.Frontend.parseNameEntryD] at hrun
    obtain ⟨p, s₁, hname, hrest⟩ := AM.bind_ok hrun
    obtain ⟨rfl, n, hcln, hdn⟩ := StateD_name_run hrel hname
    obtain ⟨un, s₂, hfresh, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨rfl, hbound⟩ := freshName_run hfresh
    obtain ⟨h, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨histep, hpn, hdh⟩ :=
      internNNode_istep hok hoff
        (by intro c hc
            simp only [NNodeView.children, List.mem_singleton] at hc
            subst hc; exact nview_isSome_of_denote hdn) hin
    have hdh' : denoteN s₃.store.ns h = some (n.str str) := by
      rw [hdh]
      simp only [denoteNView, denoteN_ext hdn histep.ext, Option.map_some]
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest3
    subst hs; subst hv
    refine ⟨histep.toParse hoff, hp.insertName hpn,
      { sc with names := sc.names.insert i (ConLeche.Name.str n str) }, ?_, ?_⟩
    · rw [ConLeche.Frontend.parseNameEntryD]
      simp only [hcln, ConLeche.Frontend.StateD.freshName,
        ← hrel.names.bound i, hbound, Bool.false_eq_true, if_false]
      rfl
    · exact { StateDRel.ext histep.ext hrel with
        names := (StateDRel.ext histep.ext hrel).names.insert hdh' }
  | num pre k =>
    rw [ConRon.Arena.Frontend.parseNameEntryD] at hrun
    obtain ⟨p, s₁, hname, hrest⟩ := AM.bind_ok hrun
    obtain ⟨rfl, n, hcln, hdn⟩ := StateD_name_run hrel hname
    obtain ⟨un, s₂, hfresh, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨rfl, hbound⟩ := freshName_run hfresh
    obtain ⟨h, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨histep, hpn, hdh⟩ :=
      internNNode_istep hok hoff
        (by intro c hc
            simp only [NNodeView.children, List.mem_singleton] at hc
            subst hc; exact nview_isSome_of_denote hdn) hin
    have hdh' : denoteN s₃.store.ns h = some (n.num k) := by
      rw [hdh]
      simp only [denoteNView, denoteN_ext hdn histep.ext, Option.map_some]
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest3
    subst hs; subst hv
    refine ⟨histep.toParse hoff, hp.insertName hpn,
      { sc with names := sc.names.insert i (ConLeche.Name.num n k) }, ?_, ?_⟩
    · rw [ConLeche.Frontend.parseNameEntryD]
      simp only [hcln, ConLeche.Frontend.StateD.freshName,
        ← hrel.names.bound i, hbound, Bool.false_eq_true, if_false]
      rfl
    · exact { StateDRel.ext histep.ext hrel with
        names := (StateDRel.ext histep.ext hrel).names.insert hdh' }

/-- con-leche: ConLeche/Frontend/ExportC.lean:240 parseLevelEntryD — a level
entry: four arms, each one `internLNode`.

The twin builds a level NODE where con-leche builds a `Level` constructor, so
each arm is one `internLNode_istep` (`Bridge/Frontend/Shared.lean`) and one
`denoteLView` unfolding; the children are table reads, and the guard is
`IdTableRel.bound` as in `parseNameEntryD_run`. -/
theorem parseLevelEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.LevelRec}
    (hrun : parseLevelEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseLevelEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  rw [ConRon.Arena.Frontend.parseLevelEntryD] at hrun
  obtain ⟨uf, s₀, hfresh, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hs0, hbound⟩ := freshLevel_run hfresh
  rw [hs0] at hrest
  -- the four arms differ only in the node they intern
  have hcl : ∀ (l : LIdx) (s₃ : AState) (uP : Level), IStep s s₃ → PersL l →
      denoteL s₃.store.ls l = some uP →
      ∀ {x : StateD} {t : AState},
        (pure { sd with levels := sd.levels.insert i l } : AM StateD) s₃
          = .ok (x, t) →
      (∃ lP, ConLeche.Frontend.parseLevelEntryD sc i r = .ok
          { sc with levels := sc.levels.insert i lP } ∧ lP = uP) →
      ParseStep s t ∧ PersStateD x ∧
        ∃ sc', ConLeche.Frontend.parseLevelEntryD sc i r = .ok sc' ∧
          StateDRel t.store x sc' := by
    intro l s₃ uP histep hpl hdl x t hpure hcl
    obtain ⟨hv, hs⟩ := AM.pure_ok hpure
    subst hs; subst hv
    obtain ⟨lP, hclP, rfl⟩ := hcl
    exact ⟨histep.toParse hoff, hp.insertLevel hpl,
      { sc with levels := sc.levels.insert i lP }, hclP,
      { StateDRel.ext histep.ext hrel with
        levels := (StateDRel.ext histep.ext hrel).levels.insert hdl }⟩
  have hguard : ConLeche.Frontend.StateD.freshLevel sc i = .ok () := by
    simp only [ConLeche.Frontend.StateD.freshLevel, ← hrel.levels.bound i,
      hbound, Bool.false_eq_true, if_false]
    rfl
  cases r with
  | succ u =>
    obtain ⟨lu, s₁, hlu, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, uP, hclu, hdlu⟩ := StateD_level_run hrel hlu
    rw [hs1] at hrest2
    obtain ⟨l, s₂, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨histep, hpl, hdl⟩ :=
      internLNode_istep hok hoff
        (⟨by intro c hc
             simp only [LNodeView.lchildren, List.mem_singleton] at hc
             subst hc; exact lview_isSome_of_denote hdlu,
          by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
    refine hcl l s₂ uP.succ histep hpl ?_ hrest3 ⟨uP.succ, ?_, rfl⟩
    · rw [hdl]
      simp only [denoteLView, denoteL_ext hdlu histep.ext, Option.map_some]
    · rw [ConLeche.Frontend.parseLevelEntryD]
      simp only [hguard, hclu]
      rfl
  | max a b =>
    obtain ⟨la, s₁, hla, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, aP, hcla, hdla⟩ := StateD_level_run hrel hla
    rw [hs1] at hrest2
    obtain ⟨lb, s₂, hlb, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, bP, hclb, hdlb⟩ := StateD_level_run hrel hlb
    rw [hs2] at hrest3
    obtain ⟨l, s₃, hin, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨histep, hpl, hdl⟩ :=
      internLNode_istep hok hoff
        (⟨by intro c hc
             simp only [LNodeView.lchildren, List.mem_cons,
               List.not_mem_nil, or_false] at hc
             rcases hc with rfl | rfl
             · exact lview_isSome_of_denote hdla
             · exact lview_isSome_of_denote hdlb,
          by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
    refine hcl l s₃ (Level.max aP bP) histep hpl ?_ hrest4 ⟨Level.max aP bP, ?_, rfl⟩
    · rw [hdl]
      simp only [denoteLView, opt2_eq_some_iff]
      exact ⟨aP, bP, denoteL_ext hdla histep.ext, denoteL_ext hdlb histep.ext, rfl⟩
    · rw [ConLeche.Frontend.parseLevelEntryD]
      simp only [hguard, hcla, hclb]
      rfl
  | imax a b =>
    obtain ⟨la, s₁, hla, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, aP, hcla, hdla⟩ := StateD_level_run hrel hla
    rw [hs1] at hrest2
    obtain ⟨lb, s₂, hlb, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, bP, hclb, hdlb⟩ := StateD_level_run hrel hlb
    rw [hs2] at hrest3
    obtain ⟨l, s₃, hin, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨histep, hpl, hdl⟩ :=
      internLNode_istep hok hoff
        (⟨by intro c hc
             simp only [LNodeView.lchildren, List.mem_cons,
               List.not_mem_nil, or_false] at hc
             rcases hc with rfl | rfl
             · exact lview_isSome_of_denote hdla
             · exact lview_isSome_of_denote hdlb,
          by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
    refine hcl l s₃ (Level.imax aP bP) histep hpl ?_ hrest4 ⟨Level.imax aP bP, ?_, rfl⟩
    · rw [hdl]
      simp only [denoteLView, opt2_eq_some_iff]
      exact ⟨aP, bP, denoteL_ext hdla histep.ext, denoteL_ext hdlb histep.ext, rfl⟩
    · rw [ConLeche.Frontend.parseLevelEntryD]
      simp only [hguard, hcla, hclb]
      rfl
  | param n =>
    obtain ⟨hn, s₁, hnm, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, nP, hcln, hdn⟩ := StateD_name_run hrel hnm
    rw [hs1] at hrest2
    obtain ⟨l, s₂, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨histep, hpl, hdl⟩ :=
      internLNode_istep hok hoff
        (⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
          by intro c hc
             simp only [LNodeView.nchildren, List.mem_singleton] at hc
             subst hc; exact nview_isSome_of_denote hdn⟩) hin
    refine hcl l s₂ (Level.param nP) histep hpl ?_ hrest3 ⟨Level.param nP, ?_, rfl⟩
    · rw [hdl]
      have hdn' : denoteN s₂.store.ls.ns hn = some nP := denoteN_ext hdn histep.ext
      simp only [denoteLView, hdn', Option.map_some]
    · rw [ConLeche.Frontend.parseLevelEntryD]
      simp only [hguard, hcln]
      rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:259 parseExprEntryD — **the
expression entry, and the tier's real work**: ten constructors, each resolving
its children through the three tables and interning one node.  This is where
DESIGN §8.3's "the export's sharing is preserved exactly (lesson 25)" becomes
a theorem: the table hit is the same shared node on both sides, so the
denotation of the interned handle is con-leche's own `Expr` with con-leche's
own sharing.

Ten arms, each the same four moves — read the children out of the three
tables, intern the node (`internE_istep`, `internLsNode_istep` for the `const`
arm's one level-list node), transport the children's denotations across the
append, and write the table.  The `lam`/`forallE` arms carry con-leche's own
`BinderMeta` as a VALUE (`Arena/Store.lean:348`: "`BinderMeta` and `Literal`
stay values"), so `parsePwD_run`'s equation is all they need of it. -/
theorem parseExprEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.ExprRec}
    (hrun : parseExprEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseExprEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  rw [ConRon.Arena.Frontend.parseExprEntryD] at hrun
  obtain ⟨uf, s₀, hfresh, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hs0, hbound⟩ := freshExpr_run hfresh
  rw [hs0] at hrest
  have hguard : ConLeche.Frontend.StateD.freshExpr sc i = .ok () := by
    simp only [ConLeche.Frontend.StateD.freshExpr, ← hrel.exprs.bound i,
      hbound, Bool.false_eq_true, if_false]
    rfl
  -- the ten arms differ only in the node they intern and its children
  have hcl : ∀ (e : EIdx) (s₃ : AState) (eP : Expr), IStep s s₃ → PersE e →
      denoteE s₃.store e = some eP →
      ∀ {x : StateD} {t : AState},
        (pure { sd with exprs := sd.exprs.insert i e } : AM StateD) s₃
          = .ok (x, t) →
      ConLeche.Frontend.parseExprEntryD sc i r
          = .ok { sc with exprs := sc.exprs.insert i eP } →
      ParseStep s t ∧ PersStateD x ∧
        ∃ sc', ConLeche.Frontend.parseExprEntryD sc i r = .ok sc' ∧
          StateDRel t.store x sc' := by
    intro e s₃ eP histep hpe hde x t hpure hclP
    obtain ⟨hv, hs⟩ := AM.pure_ok hpure
    subst hs; subst hv
    exact ⟨histep.toParse hoff, hp.insertExpr hpe,
      { sc with exprs := sc.exprs.insert i eP }, hclP,
      { StateDRel.ext histep.ext hrel with
        exprs := (StateDRel.ext histep.ext hrel).exprs.insert hde }⟩
  cases r with
  | bvar k =>
    obtain ⟨e, s₁, hin, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨histep, hpe, hde⟩ := internE_istep hok hoff viewOK_bvar hin
    refine hcl e s₁ (.bvar k) histep hpe (by rw [hde]; rfl) hrest2 ?_
    rw [ConLeche.Frontend.parseExprEntryD]
    simp only [hguard, ConLeche.Expr.mkBvar_eq]
    rfl
  | natVal k =>
    obtain ⟨e, s₁, hin, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨histep, hpe, hde⟩ := internE_istep hok hoff viewOK_lit hin
    refine hcl e s₁ (.lit (.natVal k)) histep hpe (by rw [hde]; rfl) hrest2 ?_
    rw [ConLeche.Frontend.parseExprEntryD]
    simp only [hguard]
    rfl
  | strVal str =>
    obtain ⟨e, s₁, hin, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨histep, hpe, hde⟩ := internE_istep hok hoff viewOK_lit hin
    refine hcl e s₁ (.lit (.strVal str)) histep hpe (by rw [hde]; rfl) hrest2 ?_
    rw [ConLeche.Frontend.parseExprEntryD]
    simp only [hguard]
    rfl
  | sort u =>
    obtain ⟨lu, s₁, hlu, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, uP, hclu, hdlu⟩ := StateD_level_run hrel hlu
    rw [hs1] at hrest2
    obtain ⟨e, s₂, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff (viewOK_sort (lview_isSome_of_denote hdlu)) hin
    refine hcl e s₂ (.sort uP) histep hpe ?_ hrest3 ?_
    · rw [hde]
      simp only [denoteEView, denoteL_ext hdlu histep.ext, Option.map_some]
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hclu]
      rfl
  | const n us =>
    obtain ⟨nm, s₁, hnm, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, nP, hcln, hdn⟩ := StateD_name_run hrel hnm
    rw [hs1] at hrest2
    obtain ⟨ls, s₂, hls, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, usP, hclus, hdls⟩ := StateD_levels_run hrel us hls
    rw [hs2] at hrest3
    obtain ⟨lsh, s₃, hlsn, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨histep1, hdlsh⟩ :=
      internLsNode_istep hok hoff
        (by intro c hc
            obtain ⟨u, hu⟩ := denoteLList_mem hdls c hc
            exact lview_isSome_of_denote
              (show denoteL s.store.lss.ls c = some u from hu)) hlsn
    obtain ⟨e, s₄, hin, hrest5⟩ := AM.bind_ok hrest4
    have hdlsh' : denoteLs s₃.store.lss lsh = some usP := by
      rw [hdlsh]
      exact denoteLListE_ext histep1.ext _ _ hdls
    obtain ⟨histep2, hpe, hde⟩ :=
      internE_istep histep1.ok histep1.off
        (viewOK_const (nview_isSome_of_denote (denoteN_ext hdn histep1.ext))
          (by obtain ⟨w, hw, -⟩ := Arena.denoteLs_view hdlsh'; rw [hw]; rfl)) hin
    refine hcl e s₄ (.const nP usP) (histep1.trans histep2) hpe ?_ hrest5 ?_
    · rw [hde]
      simp only [denoteEView, opt2_eq_some_iff]
      exact ⟨nP, usP, denoteN_ext hdn (histep1.ext.trans histep2.ext),
        histep2.ext.lss.lst lsh usP hdlsh', rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hcln, hclus]
      rfl
  | app f a =>
    obtain ⟨hf, s₁, hef, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, fP, hclf, hdf⟩ := StateD_expr_run hrel hef
    rw [hs1] at hrest2
    obtain ⟨ha, s₂, hea, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, aP, hcla, hda⟩ := StateD_expr_run hrel hea
    rw [hs2] at hrest3
    obtain ⟨e, s₃, hin, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff
        (viewOK_app (by rw [hdf]; rfl) (by rw [hda]; rfl)) hin
    refine hcl e s₃ (.app fP aP) histep hpe ?_ hrest4 ?_
    · rw [hde]
      simp only [denoteEView, opt2_eq_some_iff]
      exact ⟨fP, aP, denote_ext hdf histep.ext, denote_ext hda histep.ext, rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hclf, hcla]
      rfl
  | lam ty bd pw =>
    obtain ⟨hty, s₁, hety, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, tyP, hclty, hdty⟩ := StateD_expr_run hrel hety
    rw [hs1] at hrest2
    obtain ⟨hbd, s₂, hebd, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, bdP, hclbd, hdbd⟩ := StateD_expr_run hrel hebd
    rw [hs2] at hrest3
    obtain ⟨pwv, s₃, hpw, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨hs3, hclpw⟩ := parsePwD_run hok hrel hpw
    rw [hs3] at hrest4
    obtain ⟨e, s₄, hin, hrest5⟩ := AM.bind_ok hrest4
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff
        (viewOK_lam (by rw [hdty]; rfl) (by rw [hdbd]; rfl)) hin
    refine hcl e s₄ (.lam tyP bdP ⟨pwv⟩) histep hpe ?_ hrest5 ?_
    · rw [hde]
      simp only [denoteEView, opt2_eq_some_iff]
      exact ⟨tyP, bdP, denote_ext hdty histep.ext, denote_ext hdbd histep.ext,
        rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hclty, hclbd, hclpw]
      rfl
  | forallE ty bd pw =>
    obtain ⟨hty, s₁, hety, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, tyP, hclty, hdty⟩ := StateD_expr_run hrel hety
    rw [hs1] at hrest2
    obtain ⟨hbd, s₂, hebd, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, bdP, hclbd, hdbd⟩ := StateD_expr_run hrel hebd
    rw [hs2] at hrest3
    obtain ⟨pwv, s₃, hpw, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨hs3, hclpw⟩ := parsePwD_run hok hrel hpw
    rw [hs3] at hrest4
    obtain ⟨e, s₄, hin, hrest5⟩ := AM.bind_ok hrest4
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff
        (viewOK_forallE (by rw [hdty]; rfl) (by rw [hdbd]; rfl)) hin
    refine hcl e s₄ (.forallE tyP bdP ⟨pwv⟩) histep hpe ?_ hrest5 ?_
    · rw [hde]
      simp only [denoteEView, opt2_eq_some_iff]
      exact ⟨tyP, bdP, denote_ext hdty histep.ext, denote_ext hdbd histep.ext,
        rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hclty, hclbd, hclpw]
      rfl
  | letE ty vl bd =>
    obtain ⟨hty, s₁, hety, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, tyP, hclty, hdty⟩ := StateD_expr_run hrel hety
    rw [hs1] at hrest2
    obtain ⟨hvl, s₂, hevl, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, vlP, hclvl, hdvl⟩ := StateD_expr_run hrel hevl
    rw [hs2] at hrest3
    obtain ⟨hbd, s₃, hebd, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨hs3, bdP, hclbd, hdbd⟩ := StateD_expr_run hrel hebd
    rw [hs3] at hrest4
    obtain ⟨e, s₄, hin, hrest5⟩ := AM.bind_ok hrest4
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff
        (viewOK_letE (by rw [hdty]; rfl) (by rw [hdvl]; rfl)
          (by rw [hdbd]; rfl)) hin
    refine hcl e s₄ (.letE tyP vlP bdP) histep hpe ?_ hrest5 ?_
    · rw [hde]
      simp only [denoteEView, opt3_eq_some_iff]
      exact ⟨tyP, vlP, bdP, denote_ext hdty histep.ext,
        denote_ext hdvl histep.ext, denote_ext hdbd histep.ext, rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hclty, hclvl, hclbd]
      rfl
  | proj tn ix sub =>
    obtain ⟨hn, s₁, hnm, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs1, nP, hcln, hdn⟩ := StateD_name_run hrel hnm
    rw [hs1] at hrest2
    obtain ⟨hs, s₂, hes, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hs2, subP, hclsub, hdsub⟩ := StateD_expr_run hrel hes
    rw [hs2] at hrest3
    obtain ⟨e, s₃, hin, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨histep, hpe, hde⟩ :=
      internE_istep hok hoff
        (viewOK_proj (nview_isSome_of_denote hdn) (by rw [hdsub]; rfl)) hin
    refine hcl e s₃ (.proj nP ix subP) histep hpe ?_ hrest4 ?_
    · rw [hde]
      simp only [denoteEView, opt2_eq_some_iff]
      exact ⟨nP, subP, denoteN_ext hdn histep.ext,
        denote_ext hdsub histep.ext, rfl⟩
    · rw [ConLeche.Frontend.parseExprEntryD]
      simp only [hguard, hcln, hclsub]
      rfl

/-! ## The declaration records -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:284 parseCVD — a constant's
header: a name, a level-parameter list and a type.

Three reads plus `StateD_names_run`'s list induction; nothing moves. -/
theorem parseCVD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {cvr : ConLeche.Frontend.CVRec} {cv : IConstantVal}
    (hrun : parseCVD sd cvr s = .ok (cv, s')) :
    s' = s ∧ ∃ c, ConLeche.Frontend.parseCVD sc cvr = .ok c ∧
      denoteCV s.store cv = some c := by
  rw [parseCVD] at hrun
  obtain ⟨nm, s₁, hname, h1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, n, hcln, hdn⟩ := StateD_name_run hrel hname
  subst hs1
  obtain ⟨ty, s₂, hty, h2⟩ := AM.bind_ok h1
  obtain ⟨hs2, e, hclty, hdty⟩ := getDeclD_run hrel hty
  subst hs2
  obtain ⟨lps, s₃, hlps, h3⟩ := AM.bind_ok h2
  obtain ⟨hs3, xs, hcllps, hdlps⟩ := StateD_names_run hrel cvr.levelParams hlps
  subst hs3
  obtain ⟨hv, hst⟩ := AM.pure_ok h3
  subst hv; subst hst
  refine ⟨rfl, ⟨n, xs, e⟩, ?_, by simp only [denoteCV, hdn, hdlps, hdty]⟩
  rw [ConLeche.Frontend.parseCVD]
  simp only [hcln, hclty, hcllps]
  rfl

/-! ## The stored constant's common data

`IConstantInfo.toConstantVal` (`Arena/Env.lean:224-230`) is the one projection
of the environment vocabulary that is MONADIC, and round 4's finding 16 is
about why: its `.projInfo` arm builds the closed dummy type `Sort 1`, which
over handles means interning `.zero`, `.succ .zero` and `.sort one`.  Its
NAME is the stored `tbl.tableName`, and `CIProjNamed` is what ties that to
con-leche's recomputed `projTableName`. -/

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
**the three fields of a stored constant's common data denote con-leche's**, in
the `ParseStep` frame the `.projInfo` arm's three interns force. -/
theorem toConstantVal_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {ci : IConstantInfo} {c : ConstantInfo}
    (hn : CIProjNamed s.store ci)
    (hd : ConRon.Arena.Frontend.denoteCI s.store ci = some c) {v : IConstantVal}
    (hrun : IConstantInfo.toConstantVal ci s = .ok (v, s')) :
    ParseStep s s' ∧ denoteN s'.store.ns v.name = some c.toConstantVal.name ∧
      denoteNList s'.store.ns v.levelParams = some c.toConstantVal.levelParams ∧
      denoteE s'.store v.type = some c.toConstantVal.type := by
  have hcv : ∀ (w : IConstantVal) (cw : ConstantVal),
      ConRon.Arena.Frontend.denoteCV s.store w = some cw →
      denoteN s.store.ns w.name = some cw.name ∧
        denoteNList s.store.ns w.levelParams = some cw.levelParams ∧
        denoteE s.store w.type = some cw.type := by
    intro w cw hw
    simp only [ConRon.Arena.Frontend.denoteCV] at hw
    cases h1 : denoteN s.store.ns w.name with
    | none => rw [h1] at hw; simp at hw
    | some n =>
      cases h2 : ConRon.Arena.Frontend.denoteNList s.store.ns w.levelParams with
      | none => rw [h1, h2] at hw; simp at hw
      | some lps =>
        cases h3 : denoteE s.store w.type with
        | none => rw [h1, h2, h3] at hw; simp at hw
        | some ty =>
          rw [h1, h2, h3] at hw
          obtain rfl := Option.some.inj hw
          exact ⟨rfl, rfl, rfl⟩
  -- the six pure arms
  have hpure : ∀ (w : IConstantVal) (cw : ConstantVal),
      ConRon.Arena.Frontend.denoteCV s.store w = some cw →
      (pure w : AM IConstantVal) s = .ok (v, s') →
      ParseStep s s' ∧ denoteN s'.store.ns v.name = some cw.name ∧
        denoteNList s'.store.ns v.levelParams = some cw.levelParams ∧
        denoteE s'.store v.type = some cw.type := by
    intro w cw hw hr
    obtain ⟨a, b, c⟩ := hcv w cw hw
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr
    subst hvv; subst hss
    exact ⟨ParseStep.refl hok, a, b, c⟩
  cases ci with
  | axiomInfo w =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | ctorInfo w nP nF =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | defnInfo w e hh =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | thmInfo w e =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | indInfo w cps =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hc : ConRon.Arena.Frontend.denoteCaps s.store cps with
      | none => rw [hw, hc] at hd; simp at hd
      | some x =>
        rw [hw, hc] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | recInfo w mI rP rs =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hr : ConRon.Arena.Frontend.denoteRules s.store rs with
      | none => rw [hw, hr] at hd; simp at hd
      | some x =>
        rw [hw, hr] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | projInfo tbl =>
    -- the one arm that moves the store
    obtain ⟨sn, hsn, htn⟩ := hn tbl rfl
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨pt, hpt, rfl⟩ := hd
    have hlps : ConRon.Arena.Frontend.denoteNList s.store.ns tbl.levelParams
        = some pt.levelParams ∧ pt.structName = sn := by
      simp only [ConRon.Arena.Frontend.denoteProjTable, hsn] at hpt
      cases hl : ConRon.Arena.Frontend.denoteNList s.store.ns tbl.levelParams with
      | none => rw [hl] at hpt; simp at hpt
      | some lps =>
        cases hc : denoteN s.store.ns tbl.ctor with
        | none => rw [hl, hc] at hpt; simp at hpt
        | some cn =>
          cases hss : denoteL s.store.ls tbl.structSort with
          | none => rw [hl, hc, hss] at hpt; simp at hpt
          | some ss =>
            cases hbs : ConRon.Arena.Frontend.denoteEArray s.store tbl.bodies with
            | none => rw [hl, hc, hss, hbs] at hpt; simp at hpt
            | some bs =>
              cases hgs : denoteLList s.store.ls tbl.guards with
              | none => rw [hl, hc, hss, hbs, hgs] at hpt; simp at hpt
              | some gs =>
                rw [hl, hc, hss, hbs, hgs] at hpt
                obtain rfl := Option.some.inj hpt
                exact ⟨rfl, rfl⟩
    obtain ⟨hdlps, hstruct⟩ := hlps
    rw [IConstantInfo.toConstantVal] at hrun
    obtain ⟨z, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpz, hdz⟩ :=
      internLNode_istep hok hoff
        ⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h1
    have hdz' : denoteL s₁.store.ls z = some .zero := by
      rw [hdz]; rfl
    obtain ⟨one, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hpo, hdo⟩ :=
      internLNode_istep hstep1.ok hstep1.off
        ⟨by intro c hc
            simp only [LNodeView.lchildren, List.mem_singleton] at hc
            subst hc; exact lview_isSome_of_denote hdz',
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h2
    have hdo' : denoteL s₂.store.ls one = some (.succ .zero) := by
      rw [hdo]
      simp only [denoteLView, denoteL_ext hdz' hstep2.ext, Option.map_some]
    obtain ⟨ty, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, hpty, hdty⟩ :=
      internE_istep hstep2.ok hstep2.off (viewOK_sort (lview_isSome_of_denote hdo')) h3
    have hdty' : denoteE s₃.store ty = some (.sort (.succ .zero)) := by
      rw [hdty]
      simp only [denoteEView, denoteL_ext hdo' hstep3.ext, Option.map_some]
    have hx : Ext s.store s₃.store :=
      (hstep1.ext.trans hstep2.ext).trans hstep3.ext
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrest3
    subst hss; subst hvv
    refine ⟨((hstep1.trans hstep2).trans hstep3).toParse hoff, ?_, ?_, ?_⟩
    · simp only [ConstantInfo.toConstantVal, hstruct]
      exact denoteN_ext htn hx
    · exact denoteNListE_ext hx _ _ hdlps
    · exact hdty'

/-- con-leche: none — the relation `StateDRel.constTypes` carries, named once
because `noteDecl`'s fold is stated at it three times. -/
def CTRel (st : EStore) (p : List NIdx × EIdx)
    (q : List ConLeche.Name × ConLeche.Expr) : Prop :=
  denoteNList st.ns p.1 = some q.1 ∧ denoteE st p.2 = some q.2

/-- con-leche: none — the relation one entry of `noteDecl`'s working list
carries: the key denotes, the value is `StateDRel.constTypes`'s pair, and the
optional height is the same number on both sides. -/
def NoteRel (st : EStore) (p : NIdx × List NIdx × EIdx × Option Nat)
    (q : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat) : Prop :=
  denoteN st.ns p.1 = some q.1 ∧ CTRel st (p.2.1, p.2.2.1) (q.2.1, q.2.2.1) ∧
    p.2.2.2 = q.2.2.2

theorem NoteRel.ext {st st' : EStore} (hx : Ext st st')
    {p : NIdx × List NIdx × EIdx × Option Nat}
    {q : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat}
    (h : NoteRel st p q) : NoteRel st' p q :=
  ⟨denoteN_ext h.1 hx, ⟨denoteNListE_ext hx _ _ h.2.1.1, denote_ext h.2.1.2 hx⟩,
    h.2.2⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:146-147 noteDecl (the `.indDecl`
arm) — **a block's working list**, and the one arm of `noteDecl` where the
store moves: `toConstantVal` interns at a projection table. -/
theorem noteBlock_run :
    ∀ (block : List IConstantInfo) {s s' : AState} {blockP : List ConstantInfo}
      {cvs : List (NIdx × List NIdx × EIdx × Option Nat)},
      StateOK s → s.store.scratchOn = false →
      (∀ ci ∈ block, CIProjNamed s.store ci) →
      ConRon.Arena.Frontend.denoteCIList s.store block = some blockP →
      (block.mapM (m := AM) fun ci => do
        let v ← ci.toConstantVal
        pure (v.name, v.levelParams, v.type, none)) s = .ok (cvs, s') →
      ParseStep s s' ∧ ListRel (NoteRel s'.store) cvs
        (blockP.map fun ci =>
          (ci.toConstantVal.name, ci.toConstantVal.levelParams,
            ci.toConstantVal.type, (none : Option Nat))) := by
  intro block
  induction block with
  | nil =>
    intro s s' blockP cvs hok hoff _ hb hrun
    simp only [ConRon.Arena.Frontend.denoteCIList, Option.some.injEq] at hb
    subst hb
    simp only [List.mapM_nil] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨ParseStep.refl hok, .nil⟩
  | cons ci cs ih =>
    intro s s' blockP cvs hok hoff hn hb hrun
    simp only [ConRon.Arena.Frontend.denoteCIList] at hb
    cases hci : ConRon.Arena.Frontend.denoteCI s.store ci with
    | none => rw [hci] at hb; simp at hb
    | some c =>
      cases hcs : ConRon.Arena.Frontend.denoteCIList s.store cs with
      | none => rw [hci, hcs] at hb; simp at hb
      | some csP =>
        rw [hci, hcs] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        simp only [List.mapM_cons] at hrun
        obtain ⟨x, s₁, hx, hrest⟩ := AM.bind_ok hrun
        obtain ⟨v, s₂, hv, hxrest⟩ := AM.bind_ok hx
        obtain ⟨hstep1, hn1, hl1, ht1⟩ :=
          toConstantVal_run hok hoff (hn ci (by simp)) hci hv
        obtain ⟨hxv, hxs⟩ := AM.pure_ok hxrest
        subst hxs; subst hxv
        obtain ⟨ys, s₃, hmany, hrest2⟩ := AM.bind_ok hrest
        obtain ⟨hstep2, hl2⟩ :=
          ih hstep1.ok (by rw [hstep1.scratch]; exact hoff)
            (fun c' hc' => (hn c' (by simp [hc'])).mono hstep1.ext)
            (denoteCIList_ext hstep1.ext _ _ hcs) hmany
        obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest2
        subst hst2; subst hv2
        refine ⟨hstep1.trans hstep2, ?_⟩
        simp only [List.map_cons]
        exact .cons (NoteRel.ext hstep2.ext ⟨hn1, ⟨hl1, ht1⟩, rfl⟩) hl2

/-- con-leche: ConLeche/Frontend/ExportC.lean:150-152 noteDecl (the fold) —
**the declaration table's two maps, written entry by entry.**  The whole
content is `MapRel.insert` at each step, once for `constTypes` and once — only
at a `.defnDecl`'s height — for `heights`. -/
theorem noteFold_rel {st : EStore} (hwf : StoreWF st) :
    ∀ (cvs : List (NIdx × List NIdx × EIdx × Option Nat))
      (cvsP : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat)),
      ListRel (fun (p : NIdx × List NIdx × EIdx × Option Nat)
          (q : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat) =>
        denoteN st.ns p.1 = some q.1 ∧
          CTRel st (p.2.1, p.2.2.1) (q.2.1, q.2.2.1) ∧
          p.2.2.2 = q.2.2.2) cvs cvsP →
      ∀ (ct : Std.HashMap NIdx (List NIdx × EIdx)) (hs : Std.HashMap NIdx Nat)
        (ctP : Std.HashMap ConLeche.Name (List ConLeche.Name × ConLeche.Expr))
        (hsP : Std.HashMap ConLeche.Name Nat),
        MapRel st (CTRel st) ct ctP → MapRel st (fun (x y : Nat) => x = y) hs hsP →
        MapRel st (CTRel st)
            (cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs)) (ct, hs)).1
            (cvsP.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs)) (ctP, hsP)).1 ∧
          MapRel st (fun (x y : Nat) => x = y)
            (cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs)) (ct, hs)).2
            (cvsP.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs)) (ctP, hsP)).2 := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP hr ct hs ctP hsP h1 h2
    cases hr
    exact ⟨h1, h2⟩
  | cons x xs ih =>
    intro cvsP hr ct hs ctP hsP h1 h2
    cases hr with
    | cons hx hxs =>
      obtain ⟨n, lps, ty, oh⟩ := x
      rename_i y _
      obtain ⟨nP, lpsP, tyP, ohP⟩ := y
      obtain ⟨hdn, hct, hoh⟩ := hx
      simp only [List.foldl_cons]
      subst hoh
      cases oh with
      | none =>
        exact ih _ hxs _ _ _ _ (MapRel.insert hwf h1 hdn hct) h2
      | some hv =>
        exact ih _ hxs _ _ _ _ (MapRel.insert hwf h1 hdn hct)
          (MapRel.insert hwf h2 hdn rfl)

/-- con-leche: ConLeche/Frontend/ExportC.lean:137-153 noteDecl — **the
declaration table, updated.**  con-leche's is PURE and the twin's is monadic
for two reasons: `.basisDecl` fails loudly (`Arena/Frontend/ExportC.lean`'s own
note: no frontend function produces one), and — round 4's finding 16 —
`IConstantInfo.toConstantVal`'s `.projInfo` arm INTERNS.

**Round 5 repaired the statement, both halves.**

1. **The frame.**  `Arena/Env.lean:224-230`'s `.projInfo` arm runs
   `internLNode .zero`, `internLNode (.succ z)` and `internE (.sort one)`,
   because con-leche's `ConstantInfo.toConstantVal` builds the closed dummy
   type `Sort 1` as a VALUE (`ConLeche/Kernel/Env.lean:642`).  So the store
   moves at a block that holds a projection table and round 1's `s' = s` was
   not true of that run.  `ParseStep s s'` is, with the relation read at
   `s'.store` — the repair round 4 made to `projIotaLevel_run` (finding 15),
   one module over.
2. **The name.**  The twin keys `constTypes` by `v.name = tbl.tableName`, a
   STORED handle, where con-leche keys it by
   `ConLeche.projTableName tbl.structName`; `denoteProjTable` does not mention
   `tableName` at all.  `DeclProjNamed` (`Bridge/Frontend/Rel.lean`) is
   exactly the fact that ties the two, it is a hypothesis here, and
   `StateDRel.projNamed` is what carries it to this theorem's callers without
   a side condition propagating to the capstone.

`toConstantVal_run` at the block, `noteFold_rel` at the two maps. -/
theorem noteDecl_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {d : IDeclaration} {dP : Declaration}
    (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hp : PersStateD sd)
    (hrun : noteDecl sd d s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      StateDRel s'.store sd' (ConLeche.Frontend.noteDecl sc dP) := by
  have key : ∀ (t : AState) (cvs : List (NIdx × List NIdx × EIdx × Option Nat))
      (cvsP : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat)),
      ParseStep s t → ListRel (NoteRel t.store) cvs cvsP →
      ConLeche.Frontend.noteDecl sc dP
        = { sc with
            constTypes := (cvsP.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs))
              (sc.constTypes, sc.heights)).1,
            heights := (cvsP.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs))
              (sc.constTypes, sc.heights)).2 } →
      sd' = { sd with
            constTypes := (cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs))
              (sd.constTypes, sd.heights)).1,
            heights := (cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
              (ct.insert n (lps, ty),
                match h with | some h => hs.insert n h | none => hs))
              (sd.constTypes, sd.heights)).2 } →
      s' = t →
      ParseStep s s' ∧ PersStateD sd' ∧
        StateDRel s'.store sd' (ConLeche.Frontend.noteDecl sc dP) := by
    intro t cvs cvsP hstep hl hclP hsd hss
    subst hss; subst hsd
    rw [hclP]
    obtain ⟨hct, hhs⟩ := noteFold_rel hstep.ok.wf cvs cvsP hl _ _ _ _
      (StateDRel.ext hstep.ext hrel).constTypes (StateDRel.ext hstep.ext hrel).heights
    exact ⟨hstep, { hp with }, { StateDRel.ext hstep.ext hrel with
      constTypes := hct, heights := hhs }⟩
  -- the six arms whose list is a singleton, and the `.basisDecl` arm that fails
  have hone : ∀ (w : IConstantVal) (cw : ConstantVal) (oh : Option Nat),
      ConRon.Arena.Frontend.denoteCV s.store w = some cw →
      ListRel (NoteRel s.store) [(w.name, w.levelParams, w.type, oh)]
        [(cw.name, cw.levelParams, cw.type, oh)] := by
    intro w cw oh hw
    simp only [ConRon.Arena.Frontend.denoteCV] at hw
    cases h1 : denoteN s.store.ns w.name with
    | none => rw [h1] at hw; simp at hw
    | some n =>
      cases h2 : ConRon.Arena.Frontend.denoteNList s.store.ns w.levelParams with
      | none => rw [h1, h2] at hw; simp at hw
      | some lps =>
        cases h3 : denoteE s.store w.type with
        | none => rw [h1, h2, h3] at hw; simp at hw
        | some ty =>
          rw [h1, h2, h3] at hw
          obtain rfl := Option.some.inj hw
          exact .cons ⟨h1, ⟨h2, h3⟩, rfl⟩ .nil
  cases d with
  | basisDecl k =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    exact AM.fail_ok hcvs |>.elim
  | axiomDecl w =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    obtain ⟨hv, hst⟩ := AM.pure_ok hcvs
    subst hv; subst hst
    obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
    exact key _ _ _ (ParseStep.refl hok) (hone w cw none hw) rfl hv2 hst2
  | quotDecl k w =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    obtain ⟨hv, hst⟩ := AM.pure_ok hcvs
    subst hv; subst hst
    obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
    exact key _ _ _ (ParseStep.refl hok) (hone w cw none hw) rfl hv2 hst2
  | defnDecl w e hh =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        obtain ⟨hv, hst⟩ := AM.pure_ok hcvs
        subst hv; subst hst
        obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
        refine key _ _ _ (ParseStep.refl hok)
          (hone w cw (some (hintHeight hh)) hw) ?_ hv2 hst2
        cases hh <;> rfl
  | thmDecl w e =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        obtain ⟨hv, hst⟩ := AM.pure_ok hcvs
        subst hv; subst hst
        obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
        exact key _ _ _ (ParseStep.refl hok) (hone w cw none hw) rfl hv2 hst2
  | opaqueDecl w e =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        obtain ⟨hv, hst⟩ := AM.pure_ok hcvs
        subst hv; subst hst
        obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
        exact key _ _ _ (ParseStep.refl hok) (hone w cw none hw) rfl hv2 hst2
  | indDecl block nP =>
    rw [noteDecl] at hrun
    obtain ⟨cvs, t, hcvs, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨blockP, hb, rfl⟩ := hd
    obtain ⟨hstep, hl⟩ := noteBlock_run block hok hoff (hpn block nP rfl) hb hcvs
    obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
    exact key _ _ _ hstep hl rfl hv2 hst2

/-- con-leche: ConLeche/Frontend/ExportC.lean:161 pushDecl — **the record
appended, then noted.**  `pushDecl` IS `noteDecl` of the pushed record, so the
frame is `ParseStep` for `noteDecl_run`'s reason (round 4's finding 16, round
5's repair) and the `DeclProjNamed` hypothesis is the same one.

**This is the first of `StateDRel.projNamed`'s two debtors**: the pushed
record's clause is what keeps the relation's new conjunct true across the
append, and `DeclsProjNamed.push` is the whole of it.

`noteDecl_run` at the appended state. -/
theorem pushDecl_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : IDeclaration} {dP : Declaration}
    (hpd : PersDecl d) (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : pushDecl sd d s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      StateDRel s'.store sd' (ConLeche.Frontend.pushDecl sc dP) := by
  rw [pushDecl] at hrun
  rw [ConLeche.Frontend.pushDecl]
  have hone : denoteDeclArray s.store #[d] = some #[dP] := by
    rw [denoteDeclArray_iff]
    simp only [denoteDecls, hd]
  have hdecls : denoteDeclArray s.store (sd.decls.push d)
      = some (sc.decls.push dP) := by
    have h := denoteDeclArray_append hrel.decls hone
    simpa only [Array.push_eq_append] using h
  have hrel' : StateDRel s.store { sd with decls := sd.decls.push d }
      { sc with decls := sc.decls.push dP } :=
    { hrel with decls := hdecls, projNamed := hrel.projNamed.push hpn }
  have hpers : PersStateD { sd with decls := sd.decls.push d } := by
    refine { hp with decls := ?_ }
    intro x hx
    rcases Array.mem_push.mp hx with h | h
    · exact hp.decls x h
    · subst h; exact hpd
  exact noteDecl_run hok hoff hrel' hpn hd hpers hrun

/-- con-leche: ConLeche/Frontend/ExportC.lean:347 parseRuleD — one recursor
rule.

`StateD_name_run` and `getDeclD_run`; the install-computed fields carry
con-leche's own parse placeholders on both sides. -/
theorem parseRuleD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {ru : ConLeche.Frontend.RuleRec} {rl : IRecRule}
    (hrun : parseRuleD sd ru s = .ok (rl, s')) :
    s' = s ∧ ∃ r, ConLeche.Frontend.parseRuleD sc ru = .ok r ∧
      denoteRule s.store rl = some r := by
  rw [parseRuleD] at hrun
  obtain ⟨c, s₁, hname, h1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, n, hcln, hdn⟩ := StateD_name_run hrel hname
  subst hs1
  obtain ⟨rh, s₂, hrhs, h2⟩ := AM.bind_ok h1
  obtain ⟨hs2, e, hclr, hde⟩ := getDeclD_run hrel hrhs
  subst hs2
  obtain ⟨hv, hst⟩ := AM.pure_ok h2
  subst hv; subst hst
  refine ⟨rfl, RecRule.mk n ru.nfields 0 .inert e false false false, ?_,
    by simp only [denoteRule, hdn, hde, denoteFire]⟩
  rw [ConLeche.Frontend.parseRuleD]
  simp only [hcln, hclr]
  rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:346-349 parseRuleD — the rule
list, `mapM`ed: `blockRecOf`'s recursor records carry one apiece. -/
theorem parseRules_run {s : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc) :
    ∀ (rus : List ConLeche.Frontend.RuleRec) {rls : List IRecRule}
      {s' : AState}, (rus.mapM (parseRuleD sd)) s = .ok (rls, s') →
      s' = s ∧ ∃ rs, rus.mapM (ConLeche.Frontend.parseRuleD sc) = .ok rs ∧
        denoteRules s.store rls = some rs := by
  intro rus
  induction rus with
  | nil =>
    intro rls s' hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hv; subst hst
    exact ⟨rfl, [], rfl, rfl⟩
  | cons ru rus ih =>
    intro rls s' hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨rl, s₁, hone, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, r, hclr, hdr⟩ := parseRuleD_run hok hrel hone
    rw [hs1] at hrest
    obtain ⟨rls', s₂, hmany, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hs2, rs, hclrs, hdrs⟩ := ih hmany
    rw [hs2] at hrest2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hv; subst hst
    refine ⟨rfl, r :: rs, ?_, ?_⟩
    · simp only [List.mapM_cons, hclr, hclrs]
      rfl
    · simp only [denoteRules, hdr, hdrs]

/-- con-leche: ConLeche/Frontend/ExportC.lean:353-354 blockRecOf — the parsed
block, resolved, which is what the modeller seam is handed.

Three `mapM`s over `parseCVD_run` and `parseRuleD_run`; nothing moves the
store, so the three `ListRel`s of `BlockRecRel` are read off at `s` itself. -/
theorem blockRecOf_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {b : BlockRec}
    (hrun : blockRecOf sd tys cts rcs s = .ok (b, s')) :
    s' = s ∧ ∃ bP, ConLeche.Frontend.blockRecOf sc tys cts rcs = .ok bP ∧
      BlockRecRel s.store b bP := by
  -- the three member lists, each a `mapM` whose step is `parseCVD_run`
  have htys : ∀ (ts : List ConLeche.Frontend.IndTypeRec)
      {out : List MIndTypeRec} {t : AState},
      (ts.mapM fun (x : ConLeche.Frontend.IndTypeRec) => do
        pure { cv := ← parseCVD sd x.cv, nP := x.numParams, nIdx := x.numIndices,
               ctors := ← x.ctors.mapM sd.name, isRec := x.isRec,
               isReflexive := x.isReflexive,
               numNested := x.numNested : MIndTypeRec }) s = .ok (out, t) →
      t = s ∧ ∃ outP, (ts.mapM fun (x : ConLeche.Frontend.IndTypeRec) => do
        pure { cv := ← ConLeche.Frontend.parseCVD sc x.cv, nP := x.numParams,
               nIdx := x.numIndices, ctors := ← x.ctors.mapM
                 (ConLeche.Frontend.StateD.name sc),
               isRec := x.isRec, isReflexive := x.isReflexive,
               numNested := x.numNested : ConLeche.Frontend.InModel.IndTypeRec })
          = .ok outP ∧ ListRel (MIndTypeRecRel s.store) out outP := by
    intro ts
    induction ts with
    | nil =>
      intro out t hrun
      simp only [List.mapM_nil] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hv; subst hst
      exact ⟨rfl, [], rfl, .nil⟩
    | cons x xs ih =>
      intro out t hrun
      simp only [List.mapM_cons] at hrun
      obtain ⟨y, s₁, hone, hrest⟩ := AM.bind_ok hrun
      obtain ⟨cv, s₂, hcv, hone2⟩ := AM.bind_ok hone
      obtain ⟨hs2, cvP, hclcv, hdcv⟩ := parseCVD_run hok hrel hcv
      rw [hs2] at hone2
      obtain ⟨cs, s₃, hcs, hone3⟩ := AM.bind_ok hone2
      obtain ⟨hs3, csP, hclcs, hdcs⟩ := StateD_names_run hrel x.ctors hcs
      rw [hs3] at hone3
      obtain ⟨hv1, hst1⟩ := AM.pure_ok hone3
      rw [hst1] at hrest
      obtain ⟨ys, s₄, hmany, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hs4, ysP, hclys, hdys⟩ := ih hmany
      rw [hs4] at hrest2
      obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest2
      subst hv2; subst hst2; subst hv1
      refine ⟨rfl, (⟨cvP, x.numParams, x.numIndices, csP, x.isRec,
          x.isReflexive, x.numNested⟩
          : ConLeche.Frontend.InModel.IndTypeRec) :: ysP, ?_,
        .cons ⟨hdcv, rfl, rfl, hdcs, rfl, rfl, rfl⟩ hdys⟩
      simp only [List.mapM_cons, hclcv, hclcs, hclys]
      rfl
  have hcts : ∀ (ts : List ConLeche.Frontend.IndCtorRec)
      {out : List MIndCtorRec} {t : AState},
      (ts.mapM fun (x : ConLeche.Frontend.IndCtorRec) => do
        pure { cv := ← parseCVD sd x.cv, nP := x.numParams,
               nF := x.numFields : MIndCtorRec }) s = .ok (out, t) →
      t = s ∧ ∃ outP, (ts.mapM fun (x : ConLeche.Frontend.IndCtorRec) => do
        pure { cv := ← ConLeche.Frontend.parseCVD sc x.cv, nP := x.numParams,
               nF := x.numFields : ConLeche.Frontend.InModel.IndCtorRec })
          = .ok outP ∧ ListRel (MIndCtorRecRel s.store) out outP := by
    intro ts
    induction ts with
    | nil =>
      intro out t hrun
      simp only [List.mapM_nil] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hv; subst hst
      exact ⟨rfl, [], rfl, .nil⟩
    | cons x xs ih =>
      intro out t hrun
      simp only [List.mapM_cons] at hrun
      obtain ⟨y, s₁, hone, hrest⟩ := AM.bind_ok hrun
      obtain ⟨cv, s₂, hcv, hone2⟩ := AM.bind_ok hone
      obtain ⟨hs2, cvP, hclcv, hdcv⟩ := parseCVD_run hok hrel hcv
      rw [hs2] at hone2
      obtain ⟨hv1, hst1⟩ := AM.pure_ok hone2
      rw [hst1] at hrest
      obtain ⟨ys, s₄, hmany, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hs4, ysP, hclys, hdys⟩ := ih hmany
      rw [hs4] at hrest2
      obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest2
      subst hv2; subst hst2; subst hv1
      refine ⟨rfl, (⟨cvP, x.numParams, x.numFields⟩
          : ConLeche.Frontend.InModel.IndCtorRec) :: ysP, ?_,
        .cons ⟨hdcv, rfl, rfl⟩ hdys⟩
      simp only [List.mapM_cons, hclcv, hclys]
      rfl
  have hrcs : ∀ (ts : List ConLeche.Frontend.IndRecRec)
      {out : List MIndRecRec} {t : AState},
      (ts.mapM fun (x : ConLeche.Frontend.IndRecRec) => do
        let rules ← x.rules.mapM (parseRuleD sd)
        pure { cv := ← parseCVD sd x.cv, nP := x.numParams, nM := x.numMotives,
               nm := x.numMinors, nI := x.numIndices,
               rules := rules : MIndRecRec }) s = .ok (out, t) →
      t = s ∧ ∃ outP, (ts.mapM fun (x : ConLeche.Frontend.IndRecRec) => do
        let rules ← x.rules.mapM (ConLeche.Frontend.parseRuleD sc)
        pure { cv := ← ConLeche.Frontend.parseCVD sc x.cv, nP := x.numParams,
               nM := x.numMotives, nm := x.numMinors, nI := x.numIndices,
               rules := rules : ConLeche.Frontend.InModel.IndRecRec })
          = .ok outP ∧ ListRel (MIndRecRecRel s.store) out outP := by
    intro ts
    induction ts with
    | nil =>
      intro out t hrun
      simp only [List.mapM_nil] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hv; subst hst
      exact ⟨rfl, [], rfl, .nil⟩
    | cons x xs ih =>
      intro out t hrun
      simp only [List.mapM_cons] at hrun
      obtain ⟨y, s₁, hone, hrest⟩ := AM.bind_ok hrun
      obtain ⟨rls, s₂, hrls, hone2⟩ := AM.bind_ok hone
      obtain ⟨hs2, rsP, hclrs, hdrs⟩ := parseRules_run hok hrel x.rules hrls
      rw [hs2] at hone2
      obtain ⟨cv, s₃, hcv, hone3⟩ := AM.bind_ok hone2
      obtain ⟨hs3, cvP, hclcv, hdcv⟩ := parseCVD_run hok hrel hcv
      rw [hs3] at hone3
      obtain ⟨hv1, hst1⟩ := AM.pure_ok hone3
      rw [hst1] at hrest
      obtain ⟨ys, s₄, hmany, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hs4, ysP, hclys, hdys⟩ := ih hmany
      rw [hs4] at hrest2
      obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest2
      subst hv2; subst hst2; subst hv1
      refine ⟨rfl, (⟨cvP, x.numParams, x.numMotives, x.numMinors,
          x.numIndices, rsP⟩
          : ConLeche.Frontend.InModel.IndRecRec) :: ysP, ?_,
        .cons ⟨hdcv, rfl, rfl, rfl, rfl, hdrs⟩ hdys⟩
      simp only [List.mapM_cons, hclrs, hclcv, hclys]
      rfl
  rw [ConRon.Arena.Frontend.blockRecOf] at hrun
  obtain ⟨ts, s₁, hts, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hs1, tsP, hcltys, hdtys⟩ := htys tys hts
  rw [hs1] at hrest
  obtain ⟨cs, s₂, hcs, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hs2, csP, hclcts, hdcts⟩ := hcts cts hcs
  rw [hs2] at hrest2
  obtain ⟨rs, s₃, hrs, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨hs3, rsP, hclrcs, hdrcs⟩ := hrcs rcs hrs
  rw [hs3] at hrest3
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hv; subst hst
  refine ⟨rfl, ⟨tsP, csP, rsP⟩, ?_, ⟨hdtys, hdcts, hdrcs⟩⟩
  rw [ConLeche.Frontend.blockRecOf]
  simp only [hcltys, hclcts, hclrcs]
  rfl

/-- con-leche: ConLeche/Frontend/ExportC.lean:412-413 validateIndD — the half
of an `inductive` record's processing that READS: the block's redundant fields
against its own declarations.  A `.inl` answer is a verdict and the record is
rejected; a `.inr` answer is the constructor list and the declared parameter
count.

`sorry`: the guards are handle comparisons where con-leche's are `Name`
comparisons, sound by `denoteN_inj`; the arithmetic guards are equal by
`parseCVD_run`.  Task #97-P3-Frontend's sorry list, item 7. -/
theorem validateIndD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec}
    {cts' : List ConLeche.Frontend.IndCtorRec} {nPd : Nat}
    (hrun : validateIndD sd tys cts rcs s = .ok (.inr (cts', nPd), s')) :
    s' = s ∧ ConLeche.Frontend.validateIndD sc tys cts rcs = .ok (.inr (cts', nPd)) := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:564-565 installIndD — the half
that WRITES: the block's constants, the projection-owner registration and the
modeller seam.  This is the one theorem of the tier that takes the modeller's
two promises, and it takes them because `installIndD` is where the seam is
called.

`sorry`: `registerProjOwners_run` (`Bridge/Frontend/ProjRec.lean`),
`blockRecOf_run`, then `hmw`/`hmr` at the seam and `pushGenList_run` for what
it returns.  Task #97-P3-Frontend's sorry list, item 7. -/
theorem installIndD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {nPd : Nat}
    {x : StateD ⊕ RecordVerdict}
    (hrun : installIndD md sd tys cts rcs nPd s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.installIndD sc tys cts rcs nPd = .ok y ∧
        SumRel s'.store x y := by
  sorry

/-! ## The line -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:629 processLineCoreD — **the
record's own semantics**: six declaration kinds, the projection rewrite on two
of them, and the inductive route.  `Arena/Frontend/ExportC.lean`'s own note
says "every branch, guard and error string is con-leche's", and this is that
sentence as a theorem.

`sorry`: six arms over `parseCVD_run`, `getDeclD_run`, `projRewriteD_run`
(`Bridge/Frontend/ProjRec.lean`) and `pushDecl_run`, plus the `ind` arm over
`validateIndD_run` and `installIndD_run`.  Task #97-P3-Frontend's sorry list,
item 9 — **the tier's critical path**: `feedChunk` and everything above it
wait on this one. -/
theorem processLineCoreD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : ConLeche.Frontend.DeclRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : processLineCoreD md sd d s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.processLineCoreD sc d = .ok y ∧
        SumRel s'.store x y := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:710 applyDeclD — `processLineCoreD`
on both sides, by definition. -/
theorem applyDeclD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : ConLeche.Frontend.DeclRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : applyDeclD md sd d s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.applyDeclD sc d = .ok y ∧ SumRel s'.store x y :=
  processLineCoreD_run hmw hmr hok hoff hrel hp hrun

/-- con-leche: ConLeche/Frontend/ExportC.lean:719 applyLine — **THE SEMANTIC
LAYER**: one scanned line applied.  Six arms; the two trivial ones (`header`,
`blank`) are `rfl` on both sides and the scanner's record is the same value,
which is the whole point of reusing `Scan/Fast.lean` rather than twinning it.

Six arms over `parseExprEntryD_run` / `parseNameEntryD_run` /
`parseLevelEntryD_run` / `applyDeclD_run`, and two `rfl`s: the `header` and
`blank` lines move nothing on either side, which is the whole point of reusing
`Scan/Fast.lean` rather than twinning it. -/
theorem applyLine_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {r : ConLeche.Frontend.LineRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : applyLine md sd r s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.applyLine sc r = .ok y ∧ SumRel s'.store x y := by
  cases r with
  | expr i e =>
    rw [applyLine] at hrun
    obtain ⟨sd₁, s₁, hentry, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    subst hv; subst hs
    obtain ⟨hstep, hpers, sc', hcl, hrel'⟩ :=
      parseExprEntryD_run hok hoff hrel hp hentry
    exact ⟨hstep, fun _ h => by cases h; exact hpers, .inl sc',
      by rw [ConLeche.Frontend.applyLine]; simp only [hcl]; rfl,
      SumRel.of_state hrel'⟩
  | name i n =>
    rw [applyLine] at hrun
    obtain ⟨sd₁, s₁, hentry, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    subst hv; subst hs
    obtain ⟨hstep, hpers, sc', hcl, hrel'⟩ :=
      parseNameEntryD_run hok hoff hrel hp hentry
    exact ⟨hstep, fun _ h => by cases h; exact hpers, .inl sc',
      by rw [ConLeche.Frontend.applyLine]; simp only [hcl]; rfl,
      SumRel.of_state hrel'⟩
  | level i l =>
    rw [applyLine] at hrun
    obtain ⟨sd₁, s₁, hentry, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    subst hv; subst hs
    obtain ⟨hstep, hpers, sc', hcl, hrel'⟩ :=
      parseLevelEntryD_run hok hoff hrel hp hentry
    exact ⟨hstep, fun _ h => by cases h; exact hpers, .inl sc',
      by rw [ConLeche.Frontend.applyLine]; simp only [hcl]; rfl,
      SumRel.of_state hrel'⟩
  | decl d =>
    rw [applyLine] at hrun
    obtain ⟨hstep, hpers, y, hcl, hxy⟩ :=
      applyDeclD_run hmw hmr hok hoff hrel hp hrun
    exact ⟨hstep, hpers, y, by rw [ConLeche.Frontend.applyLine]; exact hcl, hxy⟩
  | header =>
    rw [applyLine] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    subst hs
    obtain rfl : x = .inl sd := hv
    exact ⟨ParseStep.refl hok, fun sd₂ h => by
      obtain rfl : sd = sd₂ := by injection h
      exact hp, .inl sc, rfl, SumRel.of_state hrel⟩
  | blank =>
    rw [applyLine] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    subst hs
    obtain rfl : x = .inl sd := hv
    exact ⟨ParseStep.refl hok, fun sd₂ h => by
      obtain rfl : sd = sd₂ := by injection h
      exact hp, .inl sc, rfl, SumRel.of_state hrel⟩

end ConRon.Bridge.Frontend

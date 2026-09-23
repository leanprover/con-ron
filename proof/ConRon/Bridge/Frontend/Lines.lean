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

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
**the TYPE half alone, which needs no name clause.**  The `.projInfo` arm's
common data is the closed dummy `Sort 1` whatever the table is called, so this
half is true of a table that is NOT rightly named, and `CIProjNamed` buys
nothing here.

Stated separately because `Bridge/Frontend/Prepare.lean`'s `usedConsts_run`
reads only the type: taking `toConstantVal_run` there would force
`DeclProjNamed` into a statement that does not need it, which is the wrong
direction for a hypothesis to travel.  The six non-projection arms are
`toConstantVal_run` at a vacuous clause; the seventh is its three interns
without the name half. -/
theorem toConstantVal_type_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {ci : IConstantInfo} {c : ConstantInfo}
    (hd : ConRon.Arena.Frontend.denoteCI s.store ci = some c) {v : IConstantVal}
    (hrun : IConstantInfo.toConstantVal ci s = .ok (v, s')) :
    ParseStep s s' ∧ denoteE s'.store v.type = some c.toConstantVal.type := by
  cases ci with
  | axiomInfo w =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | ctorInfo w nP nF =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | defnInfo w e hh =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | thmInfo w e =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | indInfo w cps =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | recInfo w mI rP rs =>
    obtain ⟨a, -, -, b⟩ :=
      toConstantVal_run hok hoff (CIProjNamed.of_ne (by simp)) hd hrun
    exact ⟨a, b⟩
  | projInfo tbl =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨pt, -, rfl⟩ := hd
    rw [IConstantInfo.toConstantVal] at hrun
    obtain ⟨z, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, -, hdz⟩ :=
      internLNode_istep hok hoff
        ⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h1
    have hdz' : denoteL s₁.store.ls z = some .zero := by rw [hdz]; rfl
    obtain ⟨one, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, -, hdo⟩ :=
      internLNode_istep hstep1.ok hstep1.off
        ⟨by intro c hc
            simp only [LNodeView.lchildren, List.mem_singleton] at hc
            subst hc; exact lview_isSome_of_denote hdz',
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h2
    have hdo' : denoteL s₂.store.ls one = some (.succ .zero) := by
      rw [hdo]
      simp only [denoteLView, denoteL_ext hdz' hstep2.ext, Option.map_some]
    obtain ⟨ty, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, -, hdty⟩ :=
      internE_istep hstep2.ok hstep2.off (viewOK_sort (lview_isSome_of_denote hdo')) h3
    have hdty' : denoteE s₃.store ty = some (.sort (.succ .zero)) := by
      rw [hdty]
      simp only [denoteEView, denoteL_ext hdo' hstep3.ext, Option.map_some]
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrest3
    subst hss; subst hvv
    exact ⟨((hstep1.trans hstep2).trans hstep3).toParse hoff, hdty'⟩

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

/-- con-leche: none — the accumulator's own step: a name pushed on both
sides.  (`Bridge/Frontend/Prepare.lean`'s `usedConsts` accumulator and
`installIndD`'s `inModelled` both read it, so it lives here, below both.) -/
theorem denoteNList_snoc {st : NStore} :
    ∀ {l : List NIdx} {lP : List ConLeche.Name} {n : NIdx}
      {nP : ConLeche.Name}, denoteNList st l = some lP →
      denoteN st n = some nP → denoteNList st (l ++ [n]) = some (lP ++ [nP]) := by
  intro l
  induction l with
  | nil =>
    intro lP n nP hl hn
    simp only [denoteNList, Option.some.injEq] at hl
    subst hl
    simp only [List.nil_append, denoteNList, hn]
  | cons a as ih =>
    intro lP n nP hl hn
    rw [denoteNList] at hl
    cases ha : denoteN st a with
    | none => rw [ha] at hl; simp at hl
    | some x =>
      cases has : denoteNList st as with
      | none => rw [ha, has] at hl; simp at hl
      | some xs =>
        rw [ha, has] at hl
        simp only [Option.some.injEq] at hl
        subst hl
        simp only [List.cons_append, denoteNList, ha, ih has hn]

/-! ## `validateIndD`'s machinery

`validateIndD` is the tier's one function written with `for` loops and early
`return`s, on both sides.  The two `do` elaborators do not produce the same
term — the twin is built with `backward.do.legacy` (an `MProd` state,
`⟨none, j, ordered⟩`) and con-leche with the new one (a `Prod` state,
`(none, ordered, j)`) — so the proof never compares loop terms: `forIn_sim`
relates a read-only `AM` loop to an `Except String` one through ANY relation on
the two states, and every step is proved by splitting the twin's branch and
taking con-leche's same branch.  The legacy elaborator inlines the
`kExpected?` join point into three copies of the recursor loop; the step is
the same in all three, so it is written once as the tactic macros below. -/

/-- con-leche: none — `Except`'s bind at a success, as a rewrite. -/
theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- con-leche: none — an `Except` bind succeeds when its head does, at an
answer the continuation accepts: the shape that lets a loop lemma name the
con-leche loop body by unification with the goal. -/
theorem except_bind_of {ε α β : Type} {m : Except ε α} {k : α → Except ε β}
    {v : β} {Q : α → Prop} {P : Prop} (hm : ∃ a, m = .ok a ∧ Q a)
    (hk : ∀ a, Q a → P ∧ k a = .ok v) : P ∧ (m >>= k) = .ok v := by
  obtain ⟨a, rfl, hq⟩ := hm
  exact hk a hq

/-- con-leche: none — `ListRel` at equality, on one list. -/
theorem ListRel.refl_eq {α : Type} : ∀ (xs : List α), ListRel (fun a b => a = b) xs xs
  | [] => ListRel.nil
  | _ :: xs => ListRel.cons rfl (ListRel.refl_eq xs)

/-- con-leche: none — a message readback in a verdict branch moves nothing:
the run continues at the same state with whatever name came back. -/
theorem readName_bind {α : Type} {h : NIdx} {f : ConLeche.Name → AM α} {s : AState}
    {p : α × AState} (hrun : (readName h >>= f) s = .ok p) :
    ∃ x, f x s = .ok p := by
  obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, -⟩ := readName_run h1
  exact ⟨x, h2⟩

/-- con-leche: none — a list related to a singleton is a singleton. -/
theorem ListRel.singleton_right {α β : Type} {P : α → β → Prop} {xs : List α} {y : β}
    (h : ListRel P xs [y]) : ∃ x, xs = [x] ∧ P x y := by
  cases h with
  | cons hxy hr => cases hr; exact ⟨_, rfl, hxy⟩

/-- con-leche: none — `except_bind_of` with the answer left existential, the
shape a loop step's obligation has. -/
theorem except_bind_ex {ε α β : Type} {m : Except ε α} {k : α → Except ε β}
    {Q : α → Prop} {P : Prop} {T : β → Prop} (hm : ∃ a, m = .ok a ∧ Q a)
    (hk : ∀ a, Q a → P ∧ ∃ v, k a = .ok v ∧ T v) :
    P ∧ ∃ v, (m >>= k) = .ok v ∧ T v := by
  obtain ⟨a, rfl, hq⟩ := hm
  exact hk a hq

/-- con-leche: none — a list related to by a singleton is a singleton. -/
theorem ListRel.singleton_left {α β : Type} {P : α → β → Prop} {x : α} {ys : List β}
    (h : ListRel P [x] ys) : ∃ y, ys = [y] ∧ P x y := by
  cases h with
  | cons hxy hr => cases hr; exact ⟨_, rfl, hxy⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:412-413 validateIndD — the two
answers agree: a verdict against a verdict of the same KIND (`VerdictRel`, the
relation the capstone reads), the validated constructors and count against
the same ones. -/
def VRes : RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat) →
    ConLeche.Frontend.RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat) → Prop
  | .inl v, .inl w => VerdictRel v w
  | .inr p, .inr q => p = q
  | _, _ => False

/-- con-leche: none — what a loop of `validateIndD` carries in its early-exit
slot: nothing, or an `.invalid` verdict, on each side.  Every `return` inside
the two loops is an `.invalid`, and this is what lets the two answers be
related without the verdict strings (which name handles on one side and names
on the other). -/
def VInv (o : Option (RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat)))
    (p : Option (ConLeche.Frontend.RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat))) :
    Prop :=
  (∀ x, o = some x → ∃ m, x = .inl (.invalid m)) ∧
    (∀ y, p = some y → ∃ m, y = .inl (.invalid m))

theorem VInv.nil : VInv none none :=
  ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩

theorem VInv.inv {m m' : String} :
    VInv (some (.inl (.invalid m))) (some (.inl (.invalid m'))) :=
  ⟨(fun _ h => by cases h; exact ⟨_, rfl⟩), (fun _ h => by cases h; exact ⟨_, rfl⟩)⟩

theorem VInv.res {a : RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat)}
    {w : ConLeche.Frontend.RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat)}
    (h : VInv (some a) (some w)) : VRes a w := by
  obtain ⟨m, rfl⟩ := h.1 a rfl
  obtain ⟨m', rfl⟩ := h.2 w rfl
  trivial

/-- con-leche: none — two `ForInStep`s agree in kind and relate. -/
def StepRel {β γ : Type} (R : β → γ → Prop) : ForInStep β → ForInStep γ → Prop
  | .yield b, .yield c => R b c
  | .done b, .done c => R b c
  | _, _ => False

/-- con-leche: none — a read-only `AM` loop against an `Except String` one. -/
theorem forIn_sim {α α' β γ : Type} {P : α → α' → Prop} {R : β → γ → Prop}
    {f : α → β → AM (ForInStep β)} {g : α' → γ → Except String (ForInStep γ)}
    {s : AState}
    (hstep : ∀ x y b c s' r, P x y → R b c → f x b s = .ok (r, s') →
        s' = s ∧ ∃ r', g y c = .ok r' ∧ StepRel R r r') :
    ∀ {xs : List α} {ys : List α'}, ListRel P xs ys →
      ∀ {b : β} {c : γ} {s' : AState} {b' : β}, R b c →
        forIn xs b f s = .ok (b', s') →
        ∃ c', forIn ys c g = .ok c' ∧ (s' = s ∧ R b' c') := by
  intro xs ys hxy
  induction hxy with
  | nil =>
    intro b c s' b' hR hrun
    rw [List.forIn_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨c, by rw [List.forIn_nil]; rfl, rfl, hR⟩
  | @cons x y xs ys hP _ ih =>
    intro b c s' b' hR hrun
    rw [List.forIn_cons] at hrun
    obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, r', hg, hsr⟩ := hstep x y b c s₁ r hP hR h1
    rw [hs1] at h2
    rw [List.forIn_cons, hg]
    cases r with
    | done b1 =>
      cases r' with
      | done c1 =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        exact ⟨c1, rfl, rfl, hsr⟩
      | yield c1 => exact absurd hsr (by simp [StepRel])
    | yield b1 =>
      cases r' with
      | yield c1 => exact ih hsr h2
      | done c1 => exact absurd hsr (by simp [StepRel])

/-- con-leche: none — a read-only `AM` `mapM` against an `Except String` one. -/
theorem mapM_sim {α β γ : Type} {P : β → γ → Prop}
    {f : α → AM β} {g : α → Except String γ} {s : AState}
    (hf : ∀ x b s', f x s = .ok (b, s') → s' = s ∧ ∃ c, g x = .ok c ∧ P b c) :
    ∀ (xs : List α) {bs : List β} {s' : AState}, xs.mapM f s = .ok (bs, s') →
      s' = s ∧ ∃ cs, xs.mapM g = .ok cs ∧ ListRel P bs cs := by
  intro xs
  induction xs with
  | nil =>
    intro bs s' hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, [], rfl, ListRel.nil⟩
  | cons x xs ih =>
    intro bs s' hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, c, hc, hbc⟩ := hf x b s₁ h1
    rw [hs1] at h2
    obtain ⟨bs', s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, cs, hcs, hrel⟩ := ih h3
    rw [hs2] at h4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
    refine ⟨rfl, c :: cs, ?_, ListRel.cons hbc hrel⟩
    simp only [List.mapM_cons, hc, hcs]
    rfl


/-- con-leche: none — `storeFuel` reads the store and moves nothing. -/
theorem storeFuel_run {s s' : AState} {n : Nat} (hrun : storeFuel s = .ok (n, s')) :
    s' = s := by
  rw [storeFuel] at hrun
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  exact (AM.pure_ok h2).2

/-- con-leche: ConLeche/Frontend/ExportC.lean:342-344 indPiTeleLen — the
constructor's own `∀`-telescope length, a read-only fuel walk. -/
theorem indPiTeleLen_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {h : EIdx} {e : Expr} (_ : denoteE s.store h = some e)
      {n : Nat} {s' : AState} (_ : indPiTeleLen fuel h s = .ok (n, s')),
      s' = s ∧ n = ConLeche.Frontend.indPiTeleLen e := by
  intro fuel
  induction fuel with
  | zero =>
    intro h e he n s' hrun
    rw [indPiTeleLen] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro h e he n s' hrun
    rw [indPiTeleLen] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview⟩ := view_run hv
    rw [hs1] at hrest
    have hde : denoteEView s.store v = some e := by
      rw [denoteE_view_eq hok.wf hview] at he; exact he
    cases v
    case forallE ty body m =>
      obtain ⟨et, eb, rfl, -, hb⟩ := denote_forallE_inv hok.wf hview he
      obtain ⟨k, s₂, hgo, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨rfl, rfl⟩ := ih hb hgo
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest2
      exact ⟨rfl, rfl⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      refine ⟨rfl, ?_⟩
      cases e with
      | forallE x y m =>
        obtain ⟨_, _, hc, -, -⟩ := denoteEView_forallE hde
        exact absurd hc (by simp)
      | _ => rfl

/-- con-leche: ConLeche/Kernel/Env.lean:583-586 Expr.piSortTeleLen? — the
read-only walk in this tier's `s' = s` frame (`Bridge/Inductives/Rel.lean`'s
`piSortTeleLen?_spec` states it at `PStep`, which is weaker than the walk). -/
theorem piSortTeleLen?_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {h : EIdx} {e : Expr} (_ : denoteE s.store h = some e)
      {o : Option Nat} {s' : AState} (_ : piSortTeleLen? fuel h s = .ok (o, s')),
      s' = s ∧ o = e.piSortTeleLen? := by
  intro fuel
  induction fuel with
  | zero =>
    intro h e he o s' hrun
    rw [piSortTeleLen?] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro h e he o s' hrun
    rw [piSortTeleLen?] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview⟩ := view_run hv
    rw [hs1] at hrest
    have hde : denoteEView s.store v = some e := by
      rw [denoteE_view_eq hok.wf hview] at he; exact he
    cases v
    case forallE ty body m =>
      obtain ⟨et, eb, rfl, -, hb⟩ := denote_forallE_inv hok.wf hview he
      obtain ⟨k, s₂, hgo, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨rfl, rfl⟩ := ih hb hgo
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest2
      exact ⟨rfl, rfl⟩
    case sort u =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hok.wf hview he
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      exact ⟨rfl, rfl⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      refine ⟨rfl, ?_⟩
      cases e with
      | forallE x y m =>
        obtain ⟨_, _, hc, -, -⟩ := denoteEView_forallE hde
        exact absurd hc (by simp)
      | sort l =>
        obtain ⟨_, hc, -⟩ := denoteEView_sort hde
        exact absurd hc (by simp)
      | _ => rfl

/-- con-leche: none — a handle in a denoting list is there exactly when its
name is in the denoted list: the function half one way, `denoteN_inj` the
other. -/
theorem ListRel.mem_iff_denoteN {st : NStore} (hw : NStoreWF st) :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      ListRel (fun h n => denoteN st h = some n) hs ns →
      ∀ {a : NIdx} {b : ConLeche.Name}, denoteN st a = some b →
        (a ∈ hs ↔ b ∈ ns) := by
  intro hs ns hr
  induction hr with
  | nil => intro a b _; simp
  | @cons x y xs ys hxy _ ih =>
    intro a b hab
    simp only [List.mem_cons, ih hab]
    constructor
    · rintro (rfl | h)
      · exact Or.inl (Option.some.inj (hab.symm.trans hxy))
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl (denoteN_inj hw hab hxy)
      · exact Or.inr h

/-- con-leche: none — the duplicate-constructor guard agrees: a handle list is
duplicate-free exactly when its denotation is (`denoteN_inj`). -/
theorem ListRel.nodup_iff_denoteN {st : NStore} (hw : NStoreWF st) :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      ListRel (fun h n => denoteN st h = some n) hs ns → (hs.Nodup ↔ ns.Nodup) := by
  intro hs ns hr
  induction hr with
  | nil => simp
  | @cons x y xs ys hxy hr ih =>
    simp only [List.nodup_cons, ih, ListRel.mem_iff_denoteN hw hr hxy]

/-- con-leche: none — `ListRel` through `flatten`. -/
theorem ListRel.flatten {α β : Type} {P : α → β → Prop} :
    ∀ {xss : List (List α)} {yss : List (List β)},
      ListRel (ListRel P) xss yss → ListRel P xss.flatten yss.flatten := by
  intro xss yss h
  induction h with
  | nil => exact ListRel.nil
  | @cons xs ys _ _ hxy _ ih =>
    simp only [List.flatten_cons]
    induction hxy with
    | nil => simpa using ih
    | cons hab _ ih2 => exact ListRel.cons hab ih2

/-- con-leche: none — `ListRel` through `zip`. -/
theorem ListRel.zip {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ} {ws : List δ},
      ListRel P xs ys → ListRel Q zs ws →
      ListRel (fun p q => P p.1 q.1 ∧ Q p.2 q.2) (xs.zip zs) (ys.zip ws) := by
  intro xs ys zs ws h1
  induction h1 generalizing zs ws with
  | nil => intro _; exact ListRel.nil
  | cons hab _ ih =>
    intro h2
    cases h2 with
    | nil => exact ListRel.nil
    | cons hcd hr => exact ListRel.cons ⟨hab, hcd⟩ (ih hr)

/-- con-leche: none — the constructor index `validateIndD` builds, keyed by
handle against con-leche's keyed by name: the two agree at every handle that
denotes (`denoteN_inj` at the insert). -/
theorem ctorIx_fold_rel {st : NStore} (hw : NStoreWF st) :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      ListRel (fun h n => denoteN st h = some n) hs ns →
      ∀ {m : Std.HashMap NIdx Nat} {mc : Std.HashMap ConLeche.Name Nat} (i : Nat),
        (∀ h n, denoteN st h = some n → m[h]? = mc[n]?) →
        ∀ h n, denoteN st h = some n →
          (hs.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
              (mi.1.insert n mi.2, mi.2 + 1)) (m, i)).1[h]?
            = (ns.foldl (fun (mi : Std.HashMap ConLeche.Name Nat × Nat) n =>
              (mi.1.insert n mi.2, mi.2 + 1)) (mc, i)).1[n]? := by
  intro hs ns hr
  induction hr with
  | nil => intro m mc i hm h n hn; exact hm h n hn
  | @cons x y xs ys hxy _ ih =>
    intro m mc i hm
    simp only [List.foldl_cons]
    apply ih
    intro h n hn
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    by_cases hxh : x = h
    · subst hxh
      obtain rfl : y = n := Option.some.inj (hxy.symm.trans hn)
      simp
    · have hyn : y ≠ n := by
        intro hc; subst hc; exact hxh (denoteN_inj hw hxy hn)
      rw [if_neg (by simpa using hxh), if_neg (by simpa using hyn)]
      exact hm h n hn


set_option hygiene false in
/-- con-leche: none — `validateIndD`'s constructor-loop step after the
`induct` guard: the constructor's own `∀`-telescope against its declared field
count. -/
macro "vind_ctor_num" : tactic => `(tactic| (
  obtain ⟨cty, s₃, hcty, hsti⟩ := AM.bind_ok hsti
  obtain ⟨hs3, ctyC, hctyC, hdcty⟩ := getDeclD_run hrel hcty
  rw [hs3] at hsti
  rw [hctyC, except_ok_bind]
  obtain ⟨tele, s₃, htele, hsti⟩ := AM.bind_ok hsti
  obtain ⟨hs3, rfl⟩ := indPiTeleLen_run hok fuel hdcty htele
  rw [hs3] at hsti
  split at hsti
  · rename_i hnf; rw [if_pos hnf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
    exact ⟨rfl, _, rfl, ⟨rfl, VInv.nil, (by show _ + 1 = _ + 1; rw [hj]), (by show Array.push _ c = Array.push _ c; rw [hord2])⟩⟩
  · rename_i hnf; rw [if_neg hnf]
    obtain ⟨x, hsti⟩ := readName_bind hsti
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
    exact ⟨rfl, _, rfl, ⟨rfl, VInv.inv, hj, hord2⟩⟩))

set_option hygiene false in
/-- con-leche: none — `validateIndD`'s constructor-loop step after the
`cidx` guard: the `induct` guard, a handle comparison against a name one
(`denoteN_inj`). -/
macro "vind_ctor_ind" : tactic => `(tactic| (
  cases hind : c.induct with
  | none =>
    simp only [hind] at hsti ⊢
    vind_ctor_num
  | some iw =>
    simp only [hind] at hsti ⊢
    obtain ⟨iwn, s₂, hiw, hsti⟩ := AM.bind_ok hsti
    obtain ⟨hs2, iwnC, hiwC, hdiw⟩ := StateD_name_run hrel hiw
    rw [hs2] at hsti
    rw [hiwC, except_ok_bind]
    have hbeq : (iwn == tn.1) = (iwnC == tnC.1) := by
      by_cases he : iwn = tn.1
      · rw [he] at hdiw
        rw [he, Option.some.inj (hdiw.symm.trans hdT), beq_self_eq_true, beq_self_eq_true]
      · have hne : iwnC ≠ tnC.1 := by
          intro hc; rw [hc] at hdiw; exact he (denoteN_inj hnw hdiw hdT)
        rw [beq_eq_false_iff_ne.mpr he, beq_eq_false_iff_ne.mpr hne]
    split at hsti
    · rename_i hiT; rw [hbeq] at hiT; rw [if_pos hiT]
      vind_ctor_num
    · rename_i hiT; rw [hbeq] at hiT; rw [if_neg hiT]
      obtain ⟨x, hsti⟩ := readName_bind hsti
      obtain ⟨x, hsti⟩ := readName_bind hsti
      obtain ⟨x, hsti⟩ := readName_bind hsti
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
      exact ⟨rfl, _, rfl, ⟨rfl, VInv.inv, hj, hord2⟩⟩))

set_option hygiene false in
/-- con-leche: none — `validateIndD`'s recursor loop, set against con-leche's: the step and the continuation are left as two goals. -/
macro "vind_rec_loop" : tactic => `(tactic| (
  obtain ⟨r2, s₂, hloop2, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex
    (forIn_sim (P := fun (a b : ConLeche.Frontend.IndRecRec) => a = b)
      (R := fun (b : MProd (Option (RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat))
          PUnit)
        (c : Option (ConLeche.Frontend.RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat)
          × Unit) =>
          b.1.isNone = c.1.isNone ∧ VInv b.1 c.1)
      ?_ (ListRel.refl_eq _) (c := (none, ())) ⟨rfl, VInv.nil⟩ hloop2) ?_))

set_option hygiene false in
/-- con-leche: none — the recursor-loop step up to the `k` guard: the name and the three count guards. -/
macro "vind_rec_head" : tactic => `(tactic| (
  subst hEq
  obtain ⟨rn, s₁, hn1, hstep⟩ := AM.bind_ok hstep
  obtain ⟨hs1, rnC, hrnC, hdrn⟩ := StateD_name_run hrel hn1
  rw [hs1] at hstep
  rw [hrnC, except_ok_bind]
  split at hstep
  rotate_left
  · rename_i hc; rw [if_neg hc]
    obtain ⟨x, hstep⟩ := readName_bind hstep
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
    exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
  rename_i hc1; rw [if_pos hc1]
  split at hstep
  rotate_left
  · rename_i hc; rw [if_neg hc]
    obtain ⟨x, hstep⟩ := readName_bind hstep
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
    exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
  rename_i hc2; rw [if_pos hc2]
  split at hstep
  rotate_left
  · rename_i hc; rw [if_neg hc]
    obtain ⟨x, hstep⟩ := readName_bind hstep
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
    exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
  rename_i hc3; rw [if_pos hc3]
))

set_option hygiene false in
/-- con-leche: none — after the recursor loop: both sides answer `.inr (cts, nPd)`. -/
macro "vind_rec_fin" : tactic => `(tactic| (
  subst s₂
  cases hr2 : r2.1 with
  | some a =>
    rw [hr2] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    obtain ⟨w, hc2⟩ : ∃ w, c2.1 = some w := by
      cases h : c2.1 with
      | none => rw [hr2, h] at hn2; exact absurd hn2 (by simp)
      | some w => exact ⟨w, rfl⟩
    rw [hc2]
    rw [hr2, hc2] at hl2
    exact ⟨rfl, _, rfl, VInv.res hl2⟩
  | none =>
    rw [hr2] at hrun
    dsimp only at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    have hc2 : c2.1 = none := by
      have h1 : c2.1.isNone = true := by rw [← hn2, hr2]; rfl
      exact Option.isNone_iff_eq_none.mp h1
    rw [hc2]
    exact ⟨rfl, _, rfl, rfl⟩))

set_option hygiene false in
/-- con-leche: none — the tail of `validateIndD`'s recursor-loop step, after
the `k` guard: the `T.rec` readback and the index-count loop.  The step is the
same in all three `kExpected?` copies the elaborator's join-point inlining
leaves, so it is written once. -/
macro "vind_rec_tail" : tactic => `(tactic| (
  obtain ⟨v, s₂, hv, hstep⟩ := AM.bind_ok hstep
  obtain ⟨hs2, hview⟩ := viewN_run hv
  rw [hs2] at hstep
  split at hstep
  · rename_i p
    obtain ⟨q, rfl, hdq⟩ := denoteN_str_inv hwr hview hdrn
    obtain ⟨r3, s₃, hloop3, hstep⟩ := AM.bind_ok hstep
    split
    rotate_left
    · rename_i hnr
      exact absurd rfl (hnr q)
    rename_i q' hq'
    obtain rfl : q = q' := by injection hq'
    refine except_bind_ex
      (forIn_sim (P := fun (a : NIdx × EIdx) (b : ConLeche.Name × Expr) =>
          denoteN s.store.ns a.1 = some b.1 ∧ denoteE s.store a.2 = some b.2)
        (R := fun (b : MProd (Option (RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat))
            PUnit)
          (c : Option (ConLeche.Frontend.RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat)
            × Unit) =>
            b.1.isNone = c.1.isNone ∧ VInv b.1 c.1)
        ?_ (ListRel.zip htyR httR) (c := (none, ())) ⟨rfl, VInv.nil⟩ hloop3) ?_
    · intro tt ttC b3 c3 s3' st3 hP3 hR3 hst3
      obtain ⟨hdn3, hde3⟩ := hP3
      have hbeq : (tt.1 == p) = (ttC.1 == q) := by
        by_cases he : tt.1 = p
        · subst he
          rw [Option.some.inj (hdn3.symm.trans hdq)]
          simp
        · have hne : ttC.1 ≠ q := by
            intro hc; subst hc; exact he (denoteN_inj hnw hdn3 hdq)
          rw [beq_eq_false_iff_ne.mpr he, beq_eq_false_iff_ne.mpr hne]
      by_cases ht : (tt.1 == p) = true
      rotate_left
      · rw [if_neg ht] at hst3; rw [hbeq] at ht; rw [if_neg ht]
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hst3
        exact ⟨rfl, _, rfl, rfl, VInv.nil⟩
      rw [if_pos ht] at hst3; rw [hbeq] at ht; rw [if_pos ht]
      obtain ⟨o, s₄, ho, hst3⟩ := AM.bind_ok hst3
      obtain ⟨hs4, rfl⟩ := piSortTeleLen?_run hok fuel hde3 ho
      rw [hs4] at hst3
      cases hpo : ttC.2.piSortTeleLen? with
      | none =>
        rw [hpo] at hst3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hst3
        exact ⟨rfl, _, rfl, rfl, VInv.nil⟩
      | some n =>
        rw [hpo] at hst3
        dsimp only at hst3 ⊢
        by_cases hn : ((List.map (fun x => x.numParams) tys).head?.getD 0 + r0.numIndices == n) = true
        · rw [if_pos hn] at hst3; rw [if_pos hn]
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hst3
          exact ⟨rfl, _, rfl, rfl, VInv.nil⟩
        · rw [if_neg hn] at hst3; rw [if_neg hn]
          obtain ⟨x, hst3⟩ := readName_bind hst3
          obtain ⟨y, hst3⟩ := readName_bind hst3
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hst3
          exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
    · rintro c3 ⟨hs3, hn3, hl3⟩
      cases hr3 : r3.1 with
      | none =>
        rw [hr3] at hstep
        have hc3 : c3.1 = none := by
          have h1 : c3.1.isNone = true := by rw [← hn3, hr3]; rfl
          exact Option.isNone_iff_eq_none.mp h1
        rw [hc3]
        dsimp only at hstep ⊢
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
        exact ⟨hs3, _, rfl, rfl, VInv.nil⟩
      | some a =>
        rw [hr3] at hstep
        obtain ⟨c3a, hc3⟩ : ∃ w, c3.1 = some w := by
          cases h : c3.1 with
          | none => rw [hr3, h] at hn3; exact absurd hn3 (by simp)
          | some w => exact ⟨w, rfl⟩
        rw [hc3]
        dsimp only at hstep ⊢
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
        refine ⟨hs3, _, rfl, rfl, ?_⟩
        rw [hr3, hc3] at hl3
        exact hl3
  · rename_i hnotrec
    split
    · rename_i T
      obtain ⟨p, rfl, -⟩ := view_str_of_denoteN hwr hview hdrn
      exact absurd rfl (hnotrec p)
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
      exact ⟨rfl, _, rfl, rfl, VInv.nil⟩))

/-- con-leche: ConLeche/Frontend/ExportC.lean:412-413 validateIndD — the half
of an `inductive` record's processing that READS: the block's redundant fields
against its own declarations.  A `.inl` answer is a verdict and the record is
rejected; a `.inr` answer is the constructor list and the declared parameter
count.

The guards are handle comparisons where con-leche's are `Name` comparisons,
sound by `denoteN_inj` (`ListRel.nodup_iff_denoteN`, `ctorIx_fold_rel`, the
`induct` and `T.rec` guards); the arithmetic guards read the same records on
both sides; the two telescope walks are `indPiTeleLen_run` and
`piSortTeleLen?_run`.  Every step is read-only, so the frame is `s' = s`.
Task #97-P3-Frontend round 7. -/
theorem validateIndD_run' {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec}
    {x : RecordVerdict ⊕ (List ConLeche.Frontend.IndCtorRec × Nat)}
    (hrun : validateIndD sd tys cts rcs s = .ok (x, s')) :
    s' = s ∧ ∃ y, ConLeche.Frontend.validateIndD sc tys cts rcs = .ok y ∧ VRes x y := by
  rw [validateIndD] at hrun
  rw [ConLeche.Frontend.validateIndD]
  simp only [pure_bind] at hrun ⊢
  by_cases hu : (tys.any fun x => x.isUnsafe) = true
  · rw [if_pos hu] at hrun; rw [if_pos hu]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, _, rfl, trivial⟩
  rw [if_neg hu] at hrun
  rw [if_neg hu]
  by_cases hall : ((List.map (fun x => x.numParams) tys).all
      fun x => x == (List.map (fun x => x.numParams) tys).head?.getD 0) = true
  rotate_left
  · rw [if_neg hall] at hrun; rw [if_neg hall]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, _, rfl, trivial⟩
  rw [if_pos hall] at hrun
  rw [if_pos hall]
  have hnw : NStoreWF s.store.ns := nsWF_of_StateOK hok
  obtain ⟨rk, hwr⟩ := nsWF_of_StateOK hok
  obtain ⟨tyNames, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, tyNamesC, htyC, htyR⟩ := mapM_sim
    (P := fun h n => denoteN s.store.ns h = some n)
    (g := fun t => ConLeche.Frontend.StateD.name sc t.cv.name)
    (fun t b s0' h => StateD_name_run hrel h) tys h1
  subst s₁
  obtain ⟨tyTypes, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, tyTypesC, httC, httR⟩ := mapM_sim
    (P := fun h e => denoteE s.store h = some e)
    (g := fun t => ConLeche.Frontend.getDeclD sc t.cv.type)
    (fun t b s0' h => getDeclD_run hrel h) tys h1
  subst s₁
  obtain ⟨listed, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, listedC, hlsC, hlsR⟩ := mapM_sim
    (P := ListRel (fun h n => denoteN s.store.ns h = some n))
    (g := fun t => t.ctors.mapM (ConLeche.Frontend.StateD.name sc))
    (fun t b s0' h => by
      obtain ⟨h1, xs, h2, h3⟩ := mapM_sim
        (P := fun h n => denoteN s.store.ns h = some n)
        (g := ConLeche.Frontend.StateD.name sc)
        (fun i b s0' h => StateD_name_run hrel h) t.ctors h
      exact ⟨h1, xs, h2, h3⟩) tys h1
  subst s₁
  obtain ⟨ctorNames, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, ctorNamesC, hcnC, hcnR⟩ := mapM_sim
    (P := fun h n => denoteN s.store.ns h = some n)
    (g := fun c => ConLeche.Frontend.StateD.name sc c.cv.name)
    (fun t b s0' h => StateD_name_run hrel h) cts h1
  subst s₁
  simp only [htyC, httC, hlsC, hcnC, except_ok_bind]
  have hflat := ListRel.flatten hlsR
  have hnd := ListRel.nodup_iff_denoteN hnw hflat
  have hlen := ListRel.length_eq hflat
  by_cases hnodup : listed.flatten.Nodup
  rotate_left
  · rw [if_neg hnodup] at hrun; rw [if_neg (fun h => hnodup (hnd.mpr h))]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, _, rfl, trivial⟩
  rw [if_pos hnodup] at hrun
  rw [if_pos (hnd.mp hnodup)]
  by_cases hlg : (listed.flatten.length == cts.length) = true
  rotate_left
  · rw [if_neg hlg] at hrun; rw [if_neg (by rw [← hlen]; exact hlg)]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, _, rfl, trivial⟩
  rw [if_pos hlg] at hrun
  rw [if_pos (by rw [← hlen]; exact hlg)]
  obtain ⟨fuel, s₁, h1, hrun⟩ := AM.bind_ok hrun
  have hs1 := storeFuel_run h1
  subst s₁
  have hIx := ctorIx_fold_rel hnw hcnR (m := ∅) (mc := ∅) 0 (by intro h n _; simp)
  obtain ⟨r, s₁, hloop, hrun⟩ := AM.bind_ok hrun
  have hz := ListRel.zip htyR hlsR
  refine except_bind_ex
    (forIn_sim (P := fun (p : NIdx × List NIdx) (q : ConLeche.Name × List ConLeche.Name) =>
        denoteN s.store.ns p.1 = some q.1 ∧
        ListRel (fun h n => denoteN s.store.ns h = some n) p.2 q.2)
      (R := fun (b : MProd (Option (RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat))
          (Array ConLeche.Frontend.IndCtorRec))
        (c : Option (ConLeche.Frontend.RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat) ×
          Array ConLeche.Frontend.IndCtorRec) =>
          b.1.isNone = c.1.isNone ∧ VInv b.1 c.1 ∧ b.2 = c.2)
      ?_ hz (c := (none, #[])) ⟨rfl, VInv.nil, rfl⟩ hloop) ?_
  · intro tn tnC b c0 s0' st hP hR hstep
    obtain ⟨hdT, hns⟩ := hP
    obtain ⟨hn0, hl0, h20⟩ := hR
    obtain ⟨ri, s₁, hin, hstep⟩ := AM.bind_ok hstep
    refine except_bind_ex
      (forIn_sim (P := fun (a : NIdx) (b : ConLeche.Name) => denoteN s.store.ns a = some b)
        (R := fun (b : MProd (Option (RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat))
            (MProd Nat (Array ConLeche.Frontend.IndCtorRec)))
          (c : Option (ConLeche.Frontend.RecordVerdict ⊕ List ConLeche.Frontend.IndCtorRec × Nat)
            × (Array ConLeche.Frontend.IndCtorRec × Nat)) =>
            b.1.isNone = c.1.isNone ∧ VInv b.1 c.1 ∧
              b.2.1 = c.2.2 ∧ b.2.2 = c.2.1)
        ?_ hns (c := (none, c0.2, 0)) ⟨rfl, VInv.nil, rfl, h20⟩ hin) ?_
    · intro n nm bi ci s0'' sti hdn hRi hsti
      obtain ⟨hni, hli, hj, hord2⟩ := hRi
      rw [← hIx n nm hdn]
      cases hk : (List.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
          (mi.1.insert n mi.2, mi.2 + 1)) (∅, 0) ctorNames).1[n]? with
      | none =>
        simp only [hk] at hsti ⊢
        obtain ⟨x, hsti⟩ := readName_bind hsti
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
        exact ⟨rfl, _, rfl, ⟨rfl, VInv.inv, hj, hord2⟩⟩
      | some k =>
        simp only [hk] at hsti ⊢
        cases hc : cts.toArray[k]? with
        | none =>
          simp only [hc] at hsti ⊢
          obtain ⟨x, hsti⟩ := readName_bind hsti
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
          exact ⟨rfl, _, rfl, ⟨rfl, VInv.inv, hj, hord2⟩⟩
        | some c =>
          simp only [hc] at hsti ⊢
          cases hcid : c.cidx with
          | none =>
            simp only [hcid] at hsti ⊢
            vind_ctor_ind
          | some ci0 =>
            simp only [hcid] at hsti ⊢
            split at hsti
            · rename_i hcj; rw [hj] at hcj; rw [if_pos hcj]
              vind_ctor_ind
            · rename_i hcj; rw [hj] at hcj; rw [if_neg hcj]
              obtain ⟨x, hsti⟩ := readName_bind hsti
              obtain ⟨x, hsti⟩ := readName_bind hsti
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hsti
              exact ⟨rfl, _, rfl, ⟨rfl, VInv.inv, hj, hord2⟩⟩
    · rintro ci ⟨hs1, hni, hli, hj, hord2⟩
      rw [hs1] at hstep
      cases hr : ri.1 with
      | none =>
        rw [hr] at hstep
        have hc : ci.1 = none := by
          have h1 : ci.1.isNone = true := by rw [← hni, hr]; rfl
          exact Option.isNone_iff_eq_none.mp h1
        rw [hc]
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
        exact ⟨rfl, _, rfl, ⟨rfl, VInv.nil, hord2⟩⟩
      | some a =>
        rw [hr] at hstep
        obtain ⟨w, hc⟩ : ∃ w, ci.1 = some w := by
          cases h : ci.1 with
          | none => rw [hr, h] at hni; exact absurd hni (by simp)
          | some w => exact ⟨w, rfl⟩
        rw [hc]
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
        rw [hr, hc] at hli
        exact ⟨rfl, _, rfl, ⟨rfl, hli, hord2⟩⟩
  · rintro c ⟨hs1, hnone, hleft, hord⟩
    subst s₁
    cases hr1 : r.1 with
    | some a =>
      rw [hr1] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      obtain ⟨w, hc1⟩ : ∃ w, c.1 = some w := by
        cases h : c.1 with
        | none => rw [hr1, h] at hnone; exact absurd hnone (by simp)
        | some w => exact ⟨w, rfl⟩
      rw [hc1]
      rw [hr1, hc1] at hleft
      exact ⟨rfl, _, rfl, VInv.res hleft⟩
    | none =>
    rw [hr1] at hrun
    dsimp only at hrun
    have hc1 : c.1 = none := by
      have h1 : c.1.isNone = true := by rw [← hnone, hr1]; rfl
      exact Option.isNone_iff_eq_none.mp h1
    rw [hc1]
    simp only []
    rw [← hord]
    generalize hO : r.snd.toList = O at hrun ⊢
    split at hrun
    · -- one type, one listed constructor, one constructor record
      rename_i ty hd1 c1
      obtain ⟨tyC, rfl, htyd⟩ := ListRel.singleton_left httR
      obtain ⟨lC, rfl, hlC⟩ := ListRel.singleton_left hlsR
      obtain ⟨hC, rfl, -⟩ := ListRel.singleton_left hlC
      obtain ⟨pr, s₂, hpr, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hs2, hdpr⟩ := piResult_run hok htyd hpr
      rw [hs2] at hrun
      obtain ⟨v, s₂, hv, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hs2, hview⟩ := view_run hv
      rw [hs2] at hrun
      split at hrun
      · -- the former's type ends in a sort: `kExpected?` reads the level
        rename_i u
        obtain ⟨l, hpil, hdl⟩ := denote_sort_inv hok.wf hview hdpr
        obtain ⟨lv, s₂, hlv, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hs2, hdlv⟩ := readLevel_run hlv
        rw [hs2] at hrun
        obtain rfl : lv = l := Option.some.inj (hdlv.symm.trans hdl)
        dsimp only
        rw [hpil]
        dsimp only
        vind_rec_loop
        · intro r0 r0' b c0 s0' st hEq hR hstep
          vind_rec_head
          split at hstep
          rotate_left
          · rename_i hk; rw [if_neg hk]
            obtain ⟨x, hstep⟩ := readName_bind hstep
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
            exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
          rename_i hk; rw [if_pos hk]
          vind_rec_tail
        · rintro c2 ⟨hs2, hn2, hl2⟩
          vind_rec_fin
      · -- it does not: `kExpected?` is `none`
        rename_i hnsort
        have hpin : ∀ l, tyC.piResult ≠ .sort l := by
          intro l hl
          rw [hl] at hdpr
          obtain ⟨u, rfl, -⟩ := denoteEView_sort (by rw [← denoteE_view_eq hok.wf hview]; exact hdpr)
          exact hnsort u rfl
        dsimp only
        vind_rec_loop
        · intro r0 r0' b c0 s0' st hEq hR hstep
          vind_rec_head
          split
          · rename_i kE0 kE heq
            exfalso
            split at heq
            · rename_i l hl
              exact hpin l hl
            · cases heq
          · vind_rec_tail
        · rintro c2 ⟨hs2, hn2, hl2⟩
          vind_rec_fin
    · -- the fallback shapes: con-leche's `kExpected?` is `some false` too
      rename_i hnot
      vind_rec_loop
      · intro r0 r0' b c0 s0' st hEq hR hstep
        vind_rec_head
        split
        · rename_i kE0 kE heq
          split at heq
          · exfalso
            obtain ⟨ty1, rfl, -⟩ := ListRel.singleton_right httR
            obtain ⟨l1, rfl, hl1⟩ := ListRel.singleton_right hlsR
            obtain ⟨hd1, rfl, -⟩ := ListRel.singleton_right hl1
            exact hnot ty1 hd1 _ rfl rfl rfl
          · obtain rfl : false = kE := Option.some.inj heq
            by_cases hk : (r0.k == false) = true
            rotate_left
            · rw [if_neg hk] at hstep; rw [if_neg hk]
              obtain ⟨x, hstep⟩ := readName_bind hstep
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hstep
              exact ⟨rfl, _, rfl, rfl, VInv.inv⟩
            rw [if_pos hk] at hstep; rw [if_pos hk]
            vind_rec_tail
        · rename_i kE0 hne
          exfalso
          apply hne false
          split
          · exfalso
            obtain ⟨ty1, rfl, -⟩ := ListRel.singleton_right httR
            obtain ⟨l1, rfl, hl1⟩ := ListRel.singleton_right hlsR
            obtain ⟨hd1, rfl, -⟩ := ListRel.singleton_right hl1
            exact hnot ty1 hd1 _ rfl rfl rfl
          · rfl
      · rintro c2 ⟨hs2, hn2, hl2⟩
        vind_rec_fin

/-- con-leche: ConLeche/Frontend/ExportC.lean:412-413 validateIndD — the
accepting arm of `validateIndD_run'`, in the shape round 1 stated. -/
theorem validateIndD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec}
    {cts' : List ConLeche.Frontend.IndCtorRec} {nPd : Nat}
    (hrun : validateIndD sd tys cts rcs s = .ok (.inr (cts', nPd), s')) :
    s' = s ∧ ConLeche.Frontend.validateIndD sc tys cts rcs = .ok (.inr (cts', nPd)) := by
  obtain ⟨hs, y, hy, hr⟩ := validateIndD_run' hok hrel hrun
  cases y with
  | inl w => exact absurd hr (by simp [VRes])
  | inr q => exact ⟨hs, by rw [hy]; cases hr; rfl⟩

/-! ## `installIndD`'s machinery

The WRITE half of an inductive record: the block's constants, the owner
census, the block map, the modeller seam and the pushes.  Everything below is
a transport of `StateDRel` through one field at a time; the two places with
content are the block map (`MapRel.foldl_insert_by`, `denoteN_inj` through
`MapRel.insert`) and the generator's context (`ctxRel_of_maps`, where the
maps' `cover` clauses become `CtxRel`'s). -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:309-317 noteProjIota — a
generated iota theorem registers its field's level.  `isProjIotaName_run` and
`projIotaLevel_run` (whose `OptRel` is exactly what `MapRel.insert` reads at
`projLevels`), nothing else. -/
theorem noteProjIota_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {cv : IConstantVal} {c : ConstantVal}
    (hcv : denoteCV s.store cv = some c)
    (hrun : noteProjIota sd cv s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      StateDRel s'.store sd' (ConLeche.Frontend.noteProjIota sc c) := by
  rw [noteProjIota] at hrun
  rw [ConLeche.Frontend.noteProjIota]
  obtain ⟨b, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, rfl⟩ := isProjIotaName_run hok (denoteCV_name hcv) h1
  rw [hs1] at hrun
  cases hb : ConLeche.Frontend.isProjIotaName c.name with
  | false =>
    rw [hb] at hrun
    simp only [Bool.false_eq_true, if_false] at hrun ⊢
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨ParseStep.refl hok, hp, hrel⟩
  | true =>
    rw [hb] at hrun
    simp only [if_true] at hrun ⊢
    obtain ⟨fuel, s₂, h2, hrun⟩ := AM.bind_ok hrun
    have hs2 := storeFuel_run h2
    rw [hs2] at hrun
    obtain ⟨o, s₃, h3, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hstep, hpl, hol⟩ := projIotaLevel_run hok hoff (denoteCV_type hcv) h3
    have hrel3 := hrel.ext hstep.ext
    cases o with
    | none =>
      have hcl := hol.none_left rfl
      rw [hcl]
      simp only [] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hstep, hp, hrel3⟩
    | some l =>
      obtain ⟨u, hu, hlu⟩ := hol.some_left rfl
      rw [hu]
      simp only [] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨hstep, { hp with }, { hrel3 with projLevels := ?_ }⟩
      exact MapRel.insert hstep.ok.wf hrel3.projLevels
        (denoteN_ext (denoteCV_name hcv) hstep.ext) hlu

/-- con-leche: ConLeche/Frontend/ExportC.lean:319-326 pushGenD — one generated
record pushed: `noteProjIota_run` at a theorem, then `pushDecl_run`. -/
theorem pushGenD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : IDeclaration} {dP : Declaration}
    (hpd : PersDecl d) (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : pushGenD sd d s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      StateDRel s'.store sd' (ConLeche.Frontend.pushGenD sc dP) := by
  cases d
  case thmDecl v e =>
    rw [pushGenD] at hrun
    obtain ⟨sd₁, s₁, h1, hrun⟩ := AM.bind_ok hrun
    have hd' := hd
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd'
    cases hv : ConRon.Arena.Frontend.denoteCV s.store v with
    | none => rw [hv] at hd'; simp at hd'
    | some c =>
      cases he : denoteE s.store e with
      | none => rw [hv, he] at hd'; simp at hd'
      | some x =>
        rw [hv, he] at hd'
        obtain rfl := Option.some.inj hd'
        obtain ⟨hstep1, hp1, hrel1⟩ := noteProjIota_run hok hoff hrel hp hv h1
        obtain ⟨hstep2, hp2, hrel2⟩ := pushDecl_run hstep1.ok
          (by rw [hstep1.scratch]; exact hoff) hrel1 hp1 hpd (hpn.mono hstep1.ext)
          (denoteDecl_ext hstep1.ext hd) hrun
        exact ⟨hstep1.trans hstep2, hp2, hrel2⟩
  all_goals
    simp only [pushGenD] at hrun
    obtain ⟨hstep, hp', hrel'⟩ := pushDecl_run hok hoff hrel hp hpd hpn hd hrun
    refine ⟨hstep, hp', ?_⟩
    cases dP with
    | thmDecl c x =>
      exfalso
      simp only [ConRon.Arena.Frontend.denoteDecl] at hd
      first
        | (simp at hd)
        | (split at hd <;> simp at hd)
    | _ => exact hrel'

/-- con-leche: none — a handle list that denotes a name list is related to it
element for element. -/
theorem ListRel.of_denoteNList {st : NStore} :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      denoteNList st hs = some ns →
      ListRel (fun h n => denoteN st h = some n) hs ns
  | [], ns, h => by
    simp only [denoteNList, Option.some.injEq] at h
    subst h; exact ListRel.nil
  | a :: as, ns, h => by
    simp only [denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        exact ListRel.cons ha (ListRel.of_denoteNList has)

/-- con-leche: none — `MapRel` through a fold of inserts of one value at every
key of a list.  `noteGen`'s owner map and `installIndD`'s block map. -/
theorem MapRel.foldl_insert {α β : Type} {st : EStore} (hwf : StoreWF st)
    {R : α → β → Prop} {v : α} {vC : β} (hv : R v vC) :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name},
      ListRel (fun h n => denoteN st.ns h = some n) ns nsC →
      ∀ {m : Std.HashMap NIdx α} {mc : Std.HashMap ConLeche.Name β},
        MapRel st R m mc →
        MapRel st R (ns.foldl (fun m n => m.insert n v) m)
          (nsC.foldl (fun m n => m.insert n vC) mc) := by
  intro ns nsC h
  induction h with
  | nil => intro m mc hm; exact hm
  | cons hab _ ih =>
    intro m mc hm
    exact ih (MapRel.insert hwf hm hab hv)

/-- con-leche: ConLeche/Frontend/ExportC.lean:328-336 noteGen — a generated
record booked: the count, and its names owned by the block.  Pure; the names
are `declNames_denote`'s. -/
theorem noteGen_run {s s' : AState} (hok : StateOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {d : IDeclaration} {dP : Declaration} (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    {T0 : NIdx} {T0C : ConLeche.Name} (hT : denoteN s.store.ns T0 = some T0C)
    (hrun : noteGen sd d T0 s = .ok (sd', s')) :
    s' = s ∧ (PersStateD sd → PersStateD sd') ∧
      StateDRel s.store sd' (ConLeche.Frontend.noteGen sc dP T0C) := by
  rw [noteGen] at hrun
  rw [ConLeche.Frontend.noteGen]
  obtain ⟨hv, hs⟩ := AM.pure_ok hrun
  subst hv
  refine ⟨hs, fun hp => { hp with }, { hrel with
    genRecords := by simp only [hrel.genRecords]
    genOwner := ?_ }⟩
  exact MapRel.foldl_insert (R := fun h n => denoteN s.store.ns h = some n) hok.wf hT
    (ListRel.of_denoteNList (declNames_denote hpn hd)) hrel.genOwner

/-- con-leche: ConLeche/Frontend/ExportC.lean:402-404 pushGenList — the
generated records, pushed and booked in order. -/
theorem pushGenList_run {T0 : NIdx} {T0C : ConLeche.Name} :
    ∀ (gen : List IDeclaration) {genP : List Declaration} {s s' : AState}
      {sd sd' : StateD} {sc : ConLeche.Frontend.StateD},
      StateOK s → s.store.scratchOn = false → StateDRel s.store sd sc →
      PersStateD sd → (∀ d ∈ gen, PersDecl d) →
      (∀ d ∈ gen, DeclProjNamed s.store d) →
      denoteDecls s.store gen = some genP → denoteN s.store.ns T0 = some T0C →
      pushGenList sd gen T0 s = .ok (sd', s') →
      ParseStep s s' ∧ PersStateD sd' ∧
        StateDRel s'.store sd' (ConLeche.Frontend.pushGenList sc genP T0C) := by
  intro gen
  induction gen with
  | nil =>
    intro genP s s' sd sd' sc hok hoff hrel hp _ _ hg _ hrun
    simp only [denoteDecls, Option.some.injEq] at hg
    subst hg
    rw [pushGenList] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨ParseStep.refl hok, hp, hrel⟩
  | cons d ds ih =>
    intro genP s s' sd sd' sc hok hoff hrel hp hpd hpn hg hT hrun
    simp only [denoteDecls] at hg
    cases hd : ConRon.Arena.Frontend.denoteDecl s.store d with
    | none => rw [hd] at hg; simp at hg
    | some dP =>
      cases hds : denoteDecls s.store ds with
      | none => rw [hd, hds] at hg; simp at hg
      | some dsP =>
        rw [hd, hds] at hg
        obtain rfl := Option.some.inj hg
        rw [pushGenList] at hrun
        obtain ⟨sd₁, s₁, h1, hrun⟩ := AM.bind_ok hrun
        obtain ⟨sd₂, s₂, h2, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hstep1, hp1, hrel1⟩ := pushGenD_run hok hoff hrel hp
          (hpd d (by simp)) (hpn d (by simp)) hd h1
        obtain ⟨hs2, hp2, hrel2⟩ := noteGen_run hstep1.ok hrel1
          ((hpn d (by simp)).mono hstep1.ext) (denoteDecl_ext hstep1.ext hd)
          (denoteN_ext hT hstep1.ext) h2
        rw [hs2] at hrun
        obtain ⟨hstep3, hp3, hrel3⟩ := ih hstep1.ok
          (by rw [hstep1.scratch]; exact hoff) hrel2 (hp2 hp1)
          (fun x hx => hpd x (by simp [hx]))
          (fun x hx => (hpn x (by simp [hx])).mono hstep1.ext)
          (denoteDecls_ext hstep1.ext ds dsP hds) (denoteN_ext hT hstep1.ext) hrun
        refine ⟨hstep1.trans hstep3, hp3, ?_⟩
        rw [ConLeche.Frontend.pushGenList]
        exact hrel3

/-- con-leche: none — `mapM_sim` with the state equation inside the
existential, the shape `except_bind_ex` consumes. -/
theorem mapM_sim' {α β γ : Type} {P : β → γ → Prop}
    {f : α → AM β} {g : α → Except String γ} {s : AState}
    (hf : ∀ x b s', f x s = .ok (b, s') → s' = s ∧ ∃ c, g x = .ok c ∧ P b c)
    (xs : List α) {bs : List β} {s' : AState} (h : xs.mapM f s = .ok (bs, s')) :
    ∃ cs, xs.mapM g = .ok cs ∧ (s' = s ∧ ListRel P bs cs) := by
  obtain ⟨h1, cs, h2, h3⟩ := mapM_sim hf xs h
  exact ⟨cs, h2, h1, h3⟩

/-- con-leche: none — `ListRel` through `++`. -/
theorem ListRel.append {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {xs' : List α} {ys' : List β},
      ListRel P xs ys → ListRel P xs' ys' → ListRel P (xs ++ xs') (ys ++ ys') := by
  intro xs ys xs' ys' h h'
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact ListRel.cons hab ih

/-- con-leche: none — a block related member for member denotes. -/
theorem denoteCIList_of_listRel {st : EStore} :
    ∀ {cs : List IConstantInfo} {csP : List ConstantInfo},
      ListRel (fun ci c => denoteCI st ci = some c ∧ ∀ t, ci ≠ .projInfo t) cs csP →
      denoteCIList st cs = some csP := by
  intro cs csP h
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [denoteCIList, hab.1, ih]

/-- con-leche: ConLeche/Kernel/Env.lean:352-371 IndCaps — the DEFAULT capability
record denotes con-leche's default, once the zero name handle decodes to
`.anonymous` (`PinsOK.anon`, task #97-P3-Ind round 5's ruling). -/
theorem denoteCaps_default {st : EStore}
    (h : denoteN st.ns (default : NIdx) = some ConLeche.Name.anonymous) :
    denoteCaps st {} = some {} := by
  simp only [denoteCaps, h]

/-- con-leche: ConLeche/Frontend/InModel.lean:36-37 wants — the modeller's
class test reads counts only. -/
theorem wants_eq {st : EStore} {b : BlockRec}
    {bP : ConLeche.Frontend.InModel.BlockRec} (h : BlockRecRel st b bP) :
    wants b = ConLeche.Frontend.InModel.wants bP := by
  rw [wants, ConLeche.Frontend.InModel.wants, ListRel.length_eq h.types]
  congr 1
  have : ∀ {ts : List MIndTypeRec} {tsP : List ConLeche.Frontend.InModel.IndTypeRec},
      ListRel (MIndTypeRecRel st) ts tsP →
      (ts.any fun x => decide (x.numNested > 0)) = (tsP.any fun x => decide (x.numNested > 0)) := by
    intro ts tsP h
    induction h with
    | nil => rfl
    | cons hab _ ih => simp only [List.any_cons, hab.numNested, ih]
  exact this h.types

/-- con-leche: none — a `MapRel` read at a handle that denotes: the two maps
answer alike (`hit` one way, `cover` and `denoteN_inj` the other). -/
theorem MapRel.getElem?_rel {α β : Type} {st : EStore} (hw : NStoreWF st.ns)
    {R : α → β → Prop} {m : Std.HashMap NIdx α} {mc : Std.HashMap ConLeche.Name β}
    (h : MapRel st R m mc) {k : NIdx} {n : ConLeche.Name}
    (hk : denoteN st.ns k = some n) : OptRel R m[k]? mc[n]? := by
  cases hm : m[k]? with
  | some a =>
    obtain ⟨n', b, hn', hb, hab⟩ := h.hit k a hm
    obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hk)
    rw [hb]; exact hab
  | none =>
    cases hc : mc[n]? with
    | none => exact OptRel.refl_none
    | some b =>
      obtain ⟨k', a, hk', ha, -⟩ := h.cover n b hc
      obtain rfl : k' = k := denoteN_inj hw hk' hk
      rw [hm] at ha; exact absurd ha (by simp)

/-- con-leche: none — `MapRel.foldl_insert` with the key read off each element
of a related list. -/
theorem MapRel.foldl_insert_by {α β γ δ : Type} {st : EStore} (hwf : StoreWF st)
    {R : α → β → Prop} {v : α} {vC : β} (hv : R v vC)
    {Q : γ → δ → Prop} {kx : γ → NIdx} {ky : δ → ConLeche.Name}
    (hk : ∀ x y, Q x y → denoteN st.ns (kx x) = some (ky y)) :
    ∀ {xs : List γ} {ys : List δ}, ListRel Q xs ys →
      ∀ {m : Std.HashMap NIdx α} {mc : Std.HashMap ConLeche.Name β},
        MapRel st R m mc →
        MapRel st R (xs.foldl (fun m x => m.insert (kx x) v) m)
          (ys.foldl (fun m y => m.insert (ky y) vC) mc) := by
  intro xs ys h
  induction h with
  | nil => intro m mc hm; exact hm
  | cons hab _ ih =>
    intro m mc hm
    exact ih (MapRel.insert hwf hm (hk _ _ hab) hv)

/-- con-leche: ConLeche/Frontend/ExportC.lean:604-605 installIndD — the
generator's context, built out of three of the parse state's maps on each
side, related: `MapRel.getElem?_rel` at the three reads and the maps' own
`cover` at the three cover clauses. -/
theorem ctxRel_of_maps {st : EStore} (hw : NStoreWF st.ns)
    {ct : Std.HashMap NIdx (List NIdx × EIdx)}
    {ctC : Std.HashMap ConLeche.Name (List ConLeche.Name × Expr)}
    {hs : Std.HashMap NIdx Nat} {hsC : Std.HashMap ConLeche.Name Nat}
    {ib : Std.HashMap NIdx BlockRec}
    {ibC : Std.HashMap ConLeche.Name ConLeche.Frontend.InModel.BlockRec}
    (h1 : MapRel st
      (fun (p : List NIdx × EIdx) (q : List ConLeche.Name × Expr) =>
        denoteNList st.ns p.1 = some q.1 ∧ denoteE st p.2 = some q.2) ct ctC)
    (h2 : MapRel st (fun (a b : Nat) => a = b) hs hsC)
    (h3 : MapRel st (BlockRecRel st) ib ibC) :
    CtxRel st ⟨fun n => ct[n]?, fun n => hs.getD n 0, fun n => ib[n]?⟩
      ⟨fun n => ctC[n]?, fun n => hsC.getD n 0, fun n => ibC[n]?⟩ where
  tbl := fun h n hn => MapRel.getElem?_rel hw h1 hn
  heights := by
    intro h n hn
    have := MapRel.getElem?_rel hw h2 hn
    simp only [Std.HashMap.getD_eq_getD_getElem?]
    cases ha : hs[h]? <;> cases hb : hsC[n]? <;> rw [ha, hb] at this <;>
      simp_all [OptRel]
  blocks := fun h n hn => MapRel.getElem?_rel hw h3 hn
  tblCover := by
    intro n q hq
    obtain ⟨h, _, hh, -, -⟩ := h1.cover n q hq
    exact ⟨h, hh⟩
  heightsCover := by
    intro n hn
    simp only [Std.HashMap.getD_eq_getD_getElem?] at hn
    cases hb : hsC[n]? with
    | none => rw [hb] at hn; exact absurd rfl hn
    | some b =>
      obtain ⟨h, _, hh, -, -⟩ := h2.cover n b hb
      exact ⟨h, hh⟩
  blocksCover := by
    intro n b hb
    obtain ⟨h, _, hh, -, -⟩ := h3.cover n b hb
    exact ⟨h, hh⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:597 installIndD — the block's
first member names the block, on both sides (`ciName_denote_of`; a parsed
block holds no `.projInfo`). -/
theorem head_name_rel {st : EStore} :
    ∀ {cs : List IConstantInfo} {csP : List ConstantInfo},
      ListRel (fun ci c => denoteCI st ci = some c ∧ ∀ t, ci ≠ .projInfo t) cs csP →
      ∀ {ci : IConstantInfo}, cs.head? = some ci →
        denoteN st.ns ci.name
          = some ((csP.head?.map (·.name)).getD ConLeche.Name.anonymous)
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab _, _, h => by
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact ciName_denote_of (CIProjNamed.of_ne hab.2) hab.1

/-- con-leche: none — every member of a related list is related to something. -/
theorem ListRel.forall_left {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel P xs ys → ∀ x ∈ xs, ∃ y, P x y := by
  intro xs ys h
  induction h with
  | nil => intro x hx; simp at hx
  | @cons a b _ _ hab _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hab⟩
    · exact ih x hx

/-- con-leche: none — the census's decline slot, updated on both sides. -/
theorem StateDRel.setDeclined {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc)
    {a : Array (NIdx × String)} {b : Array (ConLeche.Name × String)}
    (hab : ListRel (fun (p : NIdx × String) (q : ConLeche.Name × String) =>
      denoteN st.ns p.1 = some q.1 ∧ p.2 = q.2) a.toList b.toList) :
    StateDRel st { sd with inModelDeclined := a } { sc with inModelDeclined := b } :=
  { h with inModelDeclined := hab }

/-- con-leche: none — the two in-process bookkeeping slots, updated on both
sides. -/
theorem StateDRel.setModelled {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc)
    {a : Array NIdx} {b : Array ConLeche.Name}
    (hab : denoteNList st.ns a.toList = some b.toList)
    {g : Array (Nat × Array IDeclaration)} {gC : Array (Nat × Array ConLeche.Declaration)}
    (hg : ListRel
      (fun (p : Nat × Array IDeclaration) (q : Nat × Array ConLeche.Declaration) =>
        p.1 = q.1 ∧ denoteDeclArray st p.2 = some q.2) g.toList gC.toList) :
    StateDRel st { sd with inModelled := a, inModelGen := g }
      { sc with inModelled := b, inModelGen := gC } :=
  { h with inModelled := hab, inModelGen := hg }

/-- con-leche: ConLeche/Frontend/ExportC.lean:394-396 registerProjOwners — the
owner map, extended by the census on both sides (`MapRel.insert` per owner,
keyed by its own type former). -/
theorem MapRel.foldl_insert_owners {st : EStore} (hwf : StoreWF st) :
    ∀ {os : List ProjRecOwner} {osC : List ConLeche.Frontend.ProjRecOwner},
      ListRel (ProjRecOwnerRel st) os osC →
      ∀ {m : Std.HashMap NIdx ProjRecOwner}
        {mc : Std.HashMap ConLeche.Name ConLeche.Frontend.ProjRecOwner},
        MapRel st (ProjRecOwnerRel st) m mc →
        MapRel st (ProjRecOwnerRel st) (os.foldl (fun m o => m.insert o.T o) m)
          (osC.foldl (fun m o => m.insert o.T o) mc) := by
  intro os osC h
  induction h with
  | nil => intro m mc hm; exact hm
  | cons hab _ ih =>
    intro m mc hm
    exact ih (MapRel.insert hwf hm hab.T hab)

/-- con-leche: ConLeche/Frontend/ExportC.lean:379-380 registerProjOwners — the
census, recorded in the parse state's two tables.

Three `mapM`s over `parseCVD_run` (the export's shape data, related in exactly
the shape `projRecOwners_run` asks), then `projRecOwners_run` and
`MapRel.foldl_insert_owners`.  Round 7 moved it here from
`Bridge/Frontend/ProjRec.lean` (it needs `parseCVD_run`, which this module
states) and proved it from `projRecOwners_run`; it inherits that leaf's frame
finding (DESIGN, task #97-P3-Frontend round 7). -/
theorem registerProjOwners_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {block : List IConstantInfo}
    {blockP : List ConstantInfo} (hb : denoteCIList s.store block = some blockP)
    (hrun : registerProjOwners sd tys cts rcs block s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.registerProjOwners sc tys cts rcs blockP = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  suffices h : (ParseStep s s' ∧ PersStateD sd') ∧
      ∃ sc', ConLeche.Frontend.registerProjOwners sc tys cts rcs blockP = .ok sc' ∧
        StateDRel s'.store sd' sc' from ⟨h.1.1, h.1.2, h.2⟩
  rw [registerProjOwners] at hrun
  rw [ConLeche.Frontend.registerProjOwners]
  obtain ⟨types, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun (p : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)
        (q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
          List ConLeche.Name × Bool) =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧
        denoteNList s.store.ns p.2.2.2.2.2.1 = some q.2.2.2.2.2.1 ∧
        p.2.2.2.2.2.2 = q.2.2.2.2.2.2)
    (fun t b s0' h => by
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨hs, s₃, h4, h5⟩ := AM.bind_ok h3
      obtain ⟨hs4, xs, hxs, hdxs⟩ := StateD_names_run hrel t.ctors h4
      rw [hs4] at h5
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h5
      refine ⟨rfl, _, by rw [hc, except_ok_bind, hxs]; rfl, ?_⟩
      exact ⟨denoteCV_name hdc, denoteCV_lps hdc, denoteCV_type hdc, rfl, rfl, hdxs, rfl⟩)
    tys h1) ?_
  rintro typesC ⟨hs1, htR⟩
  rw [hs1] at hrun
  obtain ⟨ctors, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun (p : NIdx × Nat × EIdx) (q : ConLeche.Name × Nat × Expr) =>
      denoteN s.store.ns p.1 = some q.1 ∧ p.2.1 = q.2.1 ∧
        denoteE s.store p.2.2 = some q.2.2)
    (fun t b s0' h => by
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
      refine ⟨rfl, _, by rw [hc, except_ok_bind]; rfl, ?_⟩
      exact ⟨denoteCV_name hdc, rfl, denoteCV_type hdc⟩)
    cts h1) ?_
  rintro ctorsC ⟨hs1, hcR⟩
  rw [hs1] at hrun
  obtain ⟨recs, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun (p : NIdx × List NIdx × EIdx × Nat × Nat)
        (q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat) =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2)
    (fun t b s0' h => by
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
      refine ⟨rfl, _, by rw [hc, except_ok_bind]; rfl, ?_⟩
      exact ⟨denoteCV_name hdc, denoteCV_lps hdc, denoteCV_type hdc, rfl, rfl⟩)
    rcs h1) ?_
  rintro recsC ⟨hs1, hrR⟩
  rw [hs1] at hrun
  obtain ⟨fuel, s₁, h1, hrun⟩ := AM.bind_ok hrun
  have hs1 := storeFuel_run h1
  rw [hs1] at hrun
  obtain ⟨os, s₂, h2, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hstep, hos⟩ := projRecOwners_run hok hoff hpins hb htR hcR hrR h2
  have hrel2 := hrel.ext hstep.ext
  generalize ConLeche.Frontend.projRecOwners blockP typesC ctorsC recsC = osC at hos ⊢
  cases hos with
  | nil =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨⟨hstep, hp⟩, _, rfl, hrel2⟩
  | cons hab hrest =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨⟨hstep, { hp with }⟩, _, rfl, { hrel2 with projOwners := ?_ }⟩
    exact MapRel.foldl_insert_owners hstep.ok.wf (ListRel.cons hab hrest) hrel2.projOwners

/-- con-leche: ConLeche/Frontend/ExportC.lean:564-565 installIndD — the half
that WRITES: the block's constants, the projection-owner registration and the
modeller seam.  This is the one theorem of the tier that takes the modeller's
two promises, and it takes them because `installIndD` is where the seam is
called.

Since round 5 `hmw` carries one clause more — a generated record's projection
tables are rightly named (`DeclProjNamed`) — and that is what `pushGenList`
hands `pushDecl_run` for the records the seam returned.

`registerProjOwners_run` (above), `blockRecOf_run`,
then `hmw`/`hmr` at the seam and `pushGenList_run` for what it returns.

**Two preconditions the round-1 statement lacked** (task #97-P3-Frontend
round 7).  `PinsOK s`: the pushed `.indInfo` rows carry the DEFAULT capability
record, whose `etaCtor` is the zero name handle, and it denotes `.anonymous`
only after the pin phase (`PinsOK.anon`, the Inductives tier's round-5
ruling) — and `registerProjOwners_run` needs it for its two recognisers
anyway.  And the seam's promises were one clause short each: `ModellerWF`
now frames a DECLINING run too, and `ModellerRefines` names con-leche's
reason, because the census books it (`Bridge/Frontend/Modeller.lean`). -/
theorem installIndD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {nPd : Nat}
    {x : StateD ⊕ RecordVerdict}
    (hrun : installIndD md sd tys cts rcs nPd s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.installIndD sc tys cts rcs nPd = .ok y ∧
        SumRel s'.store x y := by
  suffices h : (ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd')) ∧
      ∃ y, ConLeche.Frontend.installIndD sc tys cts rcs nPd = .ok y ∧
        SumRel s'.store x y from ⟨h.1.1, h.1.2, h.2⟩
  rw [installIndD] at hrun
  rw [ConLeche.Frontend.installIndD]
  have hcaps := denoteCaps_default hpins.anon
  obtain ⟨types, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun ci c => denoteCI s.store ci = some c ∧ ∀ t, ci ≠ .projInfo t)
    (fun t b s0' h => by
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
      refine ⟨rfl, _, by rw [hc]; rfl, ?_, fun t h => by cases h⟩
      simp only [denoteCI, hdc, hcaps]) tys h1) ?_
  rintro typesC ⟨hs1, htR⟩
  rw [hs1] at hrun
  obtain ⟨ctors, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun ci c => denoteCI s.store ci = some c ∧ ∀ t, ci ≠ .projInfo t)
    (fun t b s0' h => by
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
      refine ⟨rfl, _, by rw [hc]; rfl, ?_, fun t h => by cases h⟩
      simp only [denoteCI, hdc]; rfl) cts h1) ?_
  rintro ctorsC ⟨hs1, hcR⟩
  rw [hs1] at hrun
  obtain ⟨recs, s₁, h1, hrun⟩ := AM.bind_ok hrun
  refine except_bind_ex (mapM_sim'
    (P := fun ci c => denoteCI s.store ci = some c ∧ ∀ t, ci ≠ .projInfo t)
    (fun t b s0' h => by
      obtain ⟨rls, s₂, h2, h3⟩ := AM.bind_ok h
      obtain ⟨hs2, rs, hrs, hdrs⟩ := parseRules_run hok hrel t.rules h2
      rw [hs2] at h3
      obtain ⟨cv, s₂, h2, h3⟩ := AM.bind_ok h3
      obtain ⟨hs2, c, hc, hdc⟩ := parseCVD_run hok hrel h2
      rw [hs2] at h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
      refine ⟨rfl, _, by rw [hrs, except_ok_bind, hc]; rfl, ?_, fun t h => by cases h⟩
      simp only [denoteCI, hdc, hdrs]) rcs h1) ?_
  rintro recsC ⟨hs1, hrR⟩
  rw [hs1] at hrun
  have hbR := ListRel.append (ListRel.append htR hcR) hrR
  have hb := denoteCIList_of_listRel hbR
  dsimp only
  obtain ⟨sd₄, s₄, h4, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hstep4, hp4, sc₄, hreg, hrel4⟩ := registerProjOwners_run hok hoff hpins hrel hp hb h4
  rw [hreg, except_ok_bind]
  have hoff4 : s₄.store.scratchOn = false := by rw [hstep4.scratch]; exact hoff
  have hbR4 := hbR.mono
    (R' := fun ci c => denoteCI s₄.store ci = some c ∧ ∀ t, ci ≠ .projInfo t)
    (fun a b h => ⟨denoteCI_ext h.1 hstep4.ext, h.2⟩)
  dsimp only at hrun
  cases hci : (types ++ ctors ++ recs).head?
  focus
    rw [hci] at hrun
    obtain ⟨T0, s₅, h5, hrun⟩ := AM.bind_ok hrun
    have hnil : types ++ ctors ++ recs = [] := List.head?_eq_none_iff.mp hci
    have hnilC : typesC ++ ctorsC ++ recsC = [] := by
      have hl := ListRel.length_eq hbR4
      rw [hnil] at hl
      exact List.eq_nil_of_length_eq_zero hl.symm
    obtain ⟨histep, -, hdn⟩ :=
      internNNode_istep hstep4.ok hoff4
        (by intro c hc; simp only [NNodeView.children] at hc; exact absurd hc (by simp)) h5
    have hstep5 : ParseStep s₄ s₅ := histep.toParse hoff4
    have hdT0 : denoteN s₅.store.ns T0 = some
        ((Option.map (fun x => x.name) (typesC ++ ctorsC ++ recsC).head?).getD
          ConLeche.Name.anonymous) := by
      rw [hdn, hnilC]; rfl
  rotate_left
  focus
    rename_i ci
    rw [hci] at hrun
    obtain ⟨T0, s₅, h5, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hv5, hs5⟩ := AM.pure_ok h5
    have hstep5 : ParseStep s₄ s₅ := ParseStep.of_eq hstep4.ok hs5
    have hdT0 := head_name_rel hbR4 hci
    rw [← hv5, ← hs5] at hdT0
  all_goals
    clear h5
    generalize hT0C : (Option.map (fun x => x.name) (typesC ++ ctorsC ++ recsC).head?).getD
      ConLeche.Name.anonymous = T0C at hdT0 ⊢
    have hrel5 := hrel4.ext hstep5.ext
    have hbR5 := hbR4.mono
      (R' := fun ci c => denoteCI s₅.store ci = some c ∧ ∀ t, ci ≠ .projInfo t)
      (fun a b h => ⟨denoteCI_ext h.1 hstep5.ext, h.2⟩)
    have hoff5 : s₅.store.scratchOn = false := by rw [hstep5.scratch]; exact hoff4
    obtain ⟨b, s₆, h6, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs6, bP, hclb, hbr⟩ := blockRecOf_run hstep5.ok hrel5 h6
    rw [hs6] at hrun
    rw [hclb, except_ok_bind]
    have hIB := MapRel.foldl_insert_by (R := BlockRecRel s₅.store) hstep5.ok.wf hbr
      (Q := MIndTypeRecRel s₅.store) (kx := fun t => t.cv.name) (ky := fun t => t.cv.name)
      (fun x y h => denoteCV_name h.cv) hbr.types hrel5.indBlocks
    have hrelB : StateDRel s₅.store
        { sd₄ with indBlocks := List.foldl (fun m t => m.insert t.cv.name b) sd₄.indBlocks b.types }
        { sc₄ with indBlocks := List.foldl (fun m t => m.insert t.cv.name bP) sc₄.indBlocks bP.types } :=
      { hrel5 with indBlocks := hIB }
    have hpB : PersStateD
        { sd₄ with indBlocks := List.foldl (fun m t => m.insert t.cv.name b) sd₄.indBlocks b.types } :=
      { hp4 with }
    have hdB : ConRon.Arena.Frontend.denoteDecl s₅.store (.indDecl (types ++ ctors ++ recs) nPd)
        = some (.indDecl (typesC ++ ctorsC ++ recsC) nPd) := by
      simp only [ConRon.Arena.Frontend.denoteDecl, denoteCIList_of_listRel hbR5]; rfl
    have hpnB : DeclProjNamed s₅.store (.indDecl (types ++ ctors ++ recs) nPd) :=
      DeclProjNamed.of_indDecl (fun ci hci => by
        obtain ⟨c, _, hne⟩ := ListRel.forall_left hbR5 ci hci
        exact CIProjNamed.of_ne hne)
    have hpdB : PersDecl (.indDecl (types ++ ctors ++ recs) nPd) :=
      PersDecl_of_denote hstep5.ok.wf hoff5 hpnB hdB
    have hcond : (sd₄.inModel && wants b) = (sc₄.inModel && ConLeche.Frontend.InModel.wants bP) := by
      rw [hrel5.inModel, wants_eq hbr]
    by_cases hc : (sc₄.inModel && ConLeche.Frontend.InModel.wants bP) = true
    rotate_left
    · rw [if_neg (by rw [hcond]; exact hc)] at hrun
      rw [if_neg hc]
      obtain ⟨sd', s₇, h7, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep7, hp7, hrel7⟩ := pushDecl_run hstep5.ok hoff5 hrelB hpB hpdB hpnB hdB h7
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨⟨hstep4.trans (hstep5.trans hstep7), fun _ h => by cases h; exact hp7⟩,
        _, rfl, hrel7⟩
    rw [if_pos (by rw [hcond]; exact hc)] at hrun
    rw [if_pos hc]
    obtain ⟨o, s₇, h7, hrun⟩ := AM.bind_ok hrun
    have hctx := ctxRel_of_maps (nsWF_of_StateOK hstep5.ok) hrel5.constTypes hrel5.heights hIB
    obtain ⟨hokh, herrh⟩ := hmr _ _ b bP s₅ o s₇ hstep5.ok hoff5 hctx hbr h7
    cases o with
    | error why =>
      rw [herrh why rfl]
      obtain ⟨hok7, hx7, hm7, hc7, hp7, hsc7⟩ := hmw.2 _ _ _ why s₇ hstep5.ok hoff5 h7
      have hstep7 : ParseStep s₅ s₇ := ParseStep.of_caches hok7 hx7 hsc7 hm7 hc7 hp7
      have hoff7 : s₇.store.scratchOn = false := by rw [hsc7]; exact hoff5
      dsimp only at hrun ⊢
      by_cases hcen : sc₄.inModelCensus = true
      · rw [if_pos (by rw [hrel5.inModelCensus]; exact hcen)] at hrun
        rw [if_pos hcen]
        obtain ⟨sd', s₈, h8, hrun⟩ := AM.bind_ok hrun
        have hrelB7 := hrelB.ext hx7
        have hdecl : ListRel
            (fun (p : NIdx × String) (q : ConLeche.Name × String) =>
              denoteN s₇.store.ns p.1 = some q.1 ∧ p.2 = q.2)
            (sd₄.inModelDeclined.push (T0, why)).toList
            (sc₄.inModelDeclined.push (T0C, why)).toList := by
          rw [Array.toList_push, Array.toList_push]
          exact ListRel.append hrelB7.inModelDeclined
            (ListRel.cons ⟨denoteN_ext hdT0 hx7, rfl⟩ ListRel.nil)
        obtain ⟨hstep8, hp8, hrel8⟩ := pushDecl_run (hrun := h8) hok7 hoff7
          (hrelB7.setDeclined hdecl) { hpB with } hpdB (hpnB.mono hx7) (denoteDecl_ext hx7 hdB)
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨⟨hstep4.trans (hstep5.trans (hstep7.trans hstep8)),
          fun _ h => by cases h; exact hp8⟩, _, rfl, hrel8⟩
      · rw [if_neg (by rw [hrel5.inModelCensus]; exact hcen)] at hrun
        rw [if_neg hcen]
        obtain ⟨nm, hrun⟩ := readName_bind hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨⟨hstep4.trans (hstep5.trans hstep7), fun _ h => by cases h⟩, _, rfl, trivial⟩
    | ok gen =>
      obtain ⟨hok7, hx7, hpers7, hnamed7, hdenS, hm7, hc7, hp7, hsc7⟩ :=
        hmw.1 _ _ _ gen s₇ hstep5.ok hoff5 h7
      obtain ⟨genP, hgenP⟩ := Option.isSome_iff_exists.mp hdenS
      rw [hokh gen rfl genP hgenP]
      have hstep7 : ParseStep s₅ s₇ := ParseStep.of_caches hok7 hx7 hsc7 hm7 hc7 hp7
      have hoff7 : s₇.store.scratchOn = false := by rw [hsc7]; exact hoff5
      dsimp only at hrun ⊢
      obtain ⟨st1, s₈, h8, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep8, hp8, hrel8⟩ := pushGenList_run gen hok7 hoff7 (hrelB.ext hx7) hpB
        hpers7 hnamed7 hgenP (denoteN_ext hdT0 hx7) h8
      have hoff8 : s₈.store.scratchOn = false := by rw [hstep8.scratch]; exact hoff7
      obtain ⟨sd', s₉, h9, hrun⟩ := AM.bind_ok hrun
      generalize hscB : ConLeche.Frontend.pushGenList
        { sc₄ with indBlocks := List.foldl (fun m t => m.insert t.cv.name bP) sc₄.indBlocks bP.types }
        genP T0C = sc8 at hrel8 ⊢
      have hmod : denoteNList s₈.store.ns (st1.inModelled.push T0).toList
          = some (sc8.inModelled.push T0C).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact denoteNList_snoc hrel8.inModelled (denoteN_ext hdT0 (hx7.trans hstep8.ext))
      have hgen8 : ListRel
          (fun (p : Nat × Array IDeclaration) (q : Nat × Array ConLeche.Declaration) =>
            p.1 = q.1 ∧ denoteDeclArray s₈.store p.2 = some q.2)
          (st1.inModelGen.push (st1.indCount - 1, gen.toArray)).toList
          (sc8.inModelGen.push (sc8.indCount - 1, genP.toArray)).toList := by
        rw [Array.toList_push, Array.toList_push]
        refine ListRel.append hrel8.inModelGen (ListRel.cons ⟨by rw [hrel8.indCount], ?_⟩ ListRel.nil)
        simp only [denoteDeclArray, denoteDecls_ext hstep8.ext gen genP hgenP,
          Option.map_some]
      obtain ⟨hstep9, hp9, hrel9⟩ := pushDecl_run (hrun := h9) hstep8.ok hoff8
        (hrel8.setModelled hmod hgen8) { hp8 with } hpdB
        ((hpnB.mono hx7).mono hstep8.ext) (denoteDecl_ext (hx7.trans hstep8.ext) hdB)
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨⟨hstep4.trans (hstep5.trans (hstep7.trans (hstep8.trans hstep9))),
        fun _ h => by cases h; exact hp9⟩, _, rfl, hrel9⟩

/-! ## The line -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:675-676 processLineCoreD — a
record the parse builds itself, pushed: the three facts `pushDecl_run` asks,
off the record's denotation. -/
theorem pushDecl_built_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : IDeclaration} {dP : Declaration}
    (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : pushDecl sd d s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      StateDRel s'.store sd' (ConLeche.Frontend.pushDecl sc dP) :=
  pushDecl_run hok hoff hrel hp (PersDecl_of_denote hok.wf hoff hpn hd) hpn hd hrun
/-- con-leche: none — the rewrite list, updated on both sides. -/
theorem StateDRel.setProjRewrites {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc)
    {a : Array NIdx} {b : Array ConLeche.Name}
    (hab : denoteNList st.ns a.toList = some b.toList) :
    StateDRel st { sd with projRewrites := a } { sc with projRewrites := b } :=
  { h with projRewrites := hab }

/-- con-leche: none — the block counter, bumped on both sides. -/
theorem StateDRel.bumpIndCount {st : EStore} {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (h : StateDRel st sd sc) :
    StateDRel st { sd with indCount := sd.indCount + 1 }
      { sc with indCount := sc.indCount + 1 } :=
  { h with indCount := by simp only [h.indCount] }

/-- con-leche: ConLeche/Frontend/ExportC.lean:629 processLineCoreD — **the
record's own semantics**: six declaration kinds, the projection rewrite on two
of them, and the inductive route.  `Arena/Frontend/ExportC.lean`'s own note
says "every branch, guard and error string is con-leche's", and this is that
sentence as a theorem.

**What round 5's repair costs this arm**: `pushDecl_run` now asks
`DeclProjNamed` of the record it pushes, and both sources have it.  A record
this function builds itself is an `.axiomDecl`/`.defnDecl`/`.thmDecl`/
`.opaqueDecl`/`.quotDecl` (`DeclProjNamed.of_…`, vacuous) or an `.indDecl`
block of `.indInfo`/`.ctorInfo`/`.recInfo` (`DeclProjNamed.of_indDecl` at a
block with no `.projInfo` in it); a record `pushGenList` pushes came from the
modeller, and `ModellerWF`'s own clause is exactly this.  **Nothing propagates
past here** — that is what putting the fact in `StateDRel.projNamed` and in
the seam's promise bought.

Six arms over `parseCVD_run`, `getDeclD_run`, `projRewriteD_run`
(`Bridge/Frontend/ProjRec.lean`, two-sided since round 7) and `pushDecl_run`,
plus the `ind` arm over `validateIndD_run'` and `installIndD_run`.  Round 7
skeletonised it: its own proof is closed, and what it rests on is
`projRewriteD_run` and `registerProjOwners_run`.  `PinsOK s` is new (round 7),
for `installIndD_run`. -/
theorem processLineCoreD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : ConLeche.Frontend.DeclRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : processLineCoreD md sd d s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.processLineCoreD sc d = .ok y ∧
        SumRel s'.store x y := by
  cases d with
  | ax cvr isUnsafe =>
    simp only [processLineCoreD] at hrun
    simp only [ConLeche.Frontend.processLineCoreD]
    obtain ⟨cvp, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, c, hc, hdc⟩ := parseCVD_run hok hrel h1
    rw [hs1] at hrun
    rw [hc, except_ok_bind]
    cases isUnsafe with
    | true =>
      simp only [if_true] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, (fun _ h => by cases h), _, rfl, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind] at hrun ⊢
      obtain ⟨sd', s₂, h2, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep, hp', hrel'⟩ := pushDecl_built_run hok hoff hrel hp
        DeclProjNamed.of_axiomDecl (by simp only [denoteDecl, hdc]; rfl) h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hstep, fun _ h => by cases h; exact hp', _, rfl, hrel'⟩
  | defn cvr value hints safety =>
    cases hints
    all_goals
      simp only [processLineCoreD] at hrun
      simp only [ConLeche.Frontend.processLineCoreD]
      obtain ⟨cvp, s₁, h1, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hs1, c, hc, hdc⟩ := parseCVD_run hok hrel h1
      rw [hs1] at hrun
      rw [hc, except_ok_bind]
      split at hrun
      · split
        rotate_left
        · exfalso; rename_i hne; first | exact hne rfl | exact hne "safe" rfl | simp at hne
        obtain ⟨vl, s₂, h2, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hs2, e, he, hde⟩ := getDeclD_run hrel h2
        rw [hs2] at hrun
        rw [he, except_ok_bind]
        obtain ⟨o, s₃, h3, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hstep3, hpe, hopt⟩ := projRewriteD_run hok hoff hrel hdc hde h3
        have hoff3 : s₃.store.scratchOn = false := by rw [hstep3.scratch]; exact hoff
        have hrel3 := hrel.ext hstep3.ext
        have hdc3 := denoteCV_ext hdc hstep3.ext
        cases o with
        | none =>
          rw [hopt.none_left rfl]
          dsimp only at hrun ⊢
          obtain ⟨sd', s₄, h4, hrun⟩ := AM.bind_ok hrun
          obtain ⟨hstep4, hp4, hrel4⟩ := pushDecl_built_run hstep3.ok hoff3 hrel3 hp
            DeclProjNamed.of_defnDecl
            (by simp only [denoteDecl, hdc3, denote_ext hde hstep3.ext]; try rfl) h4
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
          exact ⟨hstep3.trans hstep4, fun _ h => by cases h; exact hp4, _, rfl, hrel4⟩
        | some vl' =>
          obtain ⟨e', he', hde'⟩ := hopt.some_left rfl
          rw [he']
          dsimp only at hrun ⊢
          obtain ⟨sd', s₄, h4, hrun⟩ := AM.bind_ok hrun
          obtain ⟨hstep4, hp4, hrel4⟩ := pushDecl_built_run hstep3.ok hoff3 hrel3 hp
            DeclProjNamed.of_defnDecl
            (by simp only [denoteDecl, hdc3, hde']; try rfl) h4
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
          refine ⟨hstep3.trans hstep4, fun _ h => by cases h; exact { hp4 with }, _, rfl, ?_⟩
          refine hrel4.setProjRewrites ?_
          rw [Array.toList_push, Array.toList_push]
          exact denoteNList_snoc hrel4.projRewrites
            (denoteN_ext (denoteCV_name hdc) (hstep3.ext.trans hstep4.ext))
      · split
        · exfalso; rename_i hne; first | exact hne rfl | simp_all
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨ParseStep.refl hok, (fun _ h => by cases h), _, rfl, trivial⟩
  | thm cvr value =>
    simp only [processLineCoreD] at hrun
    simp only [ConLeche.Frontend.processLineCoreD]
    obtain ⟨cvp, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, c, hc, hdc⟩ := parseCVD_run hok hrel h1
    rw [hs1] at hrun
    rw [hc, except_ok_bind]
    obtain ⟨vl, s₂, h2, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs2, e, he, hde⟩ := getDeclD_run hrel h2
    rw [hs2] at hrun
    rw [he, except_ok_bind]
    obtain ⟨o, s₃, h3, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hstep3, hpe, hopt⟩ := projRewriteD_run hok hoff hrel hdc hde h3
    have hoff3 : s₃.store.scratchOn = false := by rw [hstep3.scratch]; exact hoff
    have hrel3 := hrel.ext hstep3.ext
    have hdc3 := denoteCV_ext hdc hstep3.ext
    cases o with
    | none =>
      rw [hopt.none_left rfl]
      dsimp only at hrun ⊢
      obtain ⟨sd', s₄, h4, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep4, hp4, hrel4⟩ := pushDecl_built_run hstep3.ok hoff3 hrel3 hp
        DeclProjNamed.of_thmDecl
        (by simp only [denoteDecl, hdc3, denote_ext hde hstep3.ext]; try rfl) h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hstep3.trans hstep4, fun _ h => by cases h; exact hp4, _, rfl, hrel4⟩
    | some vl' =>
      obtain ⟨e', he', hde'⟩ := hopt.some_left rfl
      rw [he']
      dsimp only at hrun ⊢
      obtain ⟨sd', s₄, h4, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep4, hp4, hrel4⟩ := pushDecl_built_run hstep3.ok hoff3 hrel3 hp
        DeclProjNamed.of_thmDecl (by simp only [denoteDecl, hdc3, hde']; try rfl) h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨hstep3.trans hstep4, fun _ h => by cases h; exact { hp4 with }, _, rfl, ?_⟩
      refine hrel4.setProjRewrites ?_
      rw [Array.toList_push, Array.toList_push]
      exact denoteNList_snoc hrel4.projRewrites
        (denoteN_ext (denoteCV_name hdc) (hstep3.ext.trans hstep4.ext))
  | opaq cvr value isUnsafe =>
    simp only [processLineCoreD] at hrun
    simp only [ConLeche.Frontend.processLineCoreD]
    obtain ⟨cvp, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, c, hc, hdc⟩ := parseCVD_run hok hrel h1
    rw [hs1] at hrun
    rw [hc, except_ok_bind]
    cases isUnsafe with
    | true =>
      simp only [if_true] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, (fun _ h => by cases h), _, rfl, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind] at hrun ⊢
      obtain ⟨vl, s₂, h2, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hs2, e, he, hde⟩ := getDeclD_run hrel h2
      rw [hs2] at hrun
      rw [he, except_ok_bind]
      obtain ⟨sd', s₃, h3, hrun⟩ := AM.bind_ok hrun
      obtain ⟨hstep, hp', hrel'⟩ := pushDecl_built_run hok hoff hrel hp
        DeclProjNamed.of_opaqueDecl (by simp only [denoteDecl, hdc, hde]; try rfl) h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hstep, fun _ h => by cases h; exact hp', _, rfl, hrel'⟩
  | quot cvr kind =>
    simp only [processLineCoreD] at hrun
    simp only [ConLeche.Frontend.processLineCoreD]
    obtain ⟨cv, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, c, hc, hdc⟩ := parseCVD_run hok hrel h1
    rw [hs1] at hrun
    rw [hc, except_ok_bind]
    split at hrun
    all_goals
      first
        | (exfalso
           obtain ⟨qk, s₂, h2, -⟩ := AM.bind_ok hrun
           exact AM.fail_ok h2)
        | (simp only [pure_bind] at hrun
           obtain ⟨sd', s₃, h3, hrun⟩ := AM.bind_ok hrun
           obtain ⟨hstep, hp', hrel'⟩ := pushDecl_built_run hok hoff hrel hp
             DeclProjNamed.of_quotDecl (by simp only [denoteDecl, hdc]; try rfl) h3
           obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
           refine ⟨hstep, fun _ h => by cases h; exact hp', ?_⟩
           split
           all_goals first
             | exact ⟨_, rfl, hrel'⟩
             | (exfalso; simp_all; done))
  | ind tys cts rcs =>
    simp only [processLineCoreD] at hrun
    simp only [ConLeche.Frontend.processLineCoreD]
    obtain ⟨v, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, y, hy, hvr⟩ := validateIndD_run' hok hrel.bumpIndCount h1
    rw [hs1] at hrun
    rw [hy, except_ok_bind]
    cases v with
    | inl v =>
      cases y with
      | inl w =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨ParseStep.refl hok, (fun _ h => by cases h), _, rfl, hvr⟩
      | inr q => exact absurd hvr (by simp [VRes])
    | inr p =>
      cases y with
      | inl w => exact absurd hvr (by simp [VRes])
      | inr q =>
        obtain rfl : p = q := hvr
        exact installIndD_run hmw hmr hok hoff hpins hrel.bumpIndCount { hp with } hrun

/-- con-leche: ConLeche/Frontend/ExportC.lean:710 applyDeclD — `processLineCoreD`
on both sides, by definition. -/
theorem applyDeclD_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : ConLeche.Frontend.DeclRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : applyDeclD md sd d s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.applyDeclD sc d = .ok y ∧ SumRel s'.store x y :=
  processLineCoreD_run hmw hmr hok hoff hpins hrel hp hrun

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
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {sd : StateD}
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
      applyDeclD_run hmw hmr hok hoff hpins hrel hp hrun
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

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

/-! ## The three entry parsers -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:229 parseNameEntryD — a name
entry: the rebinding guard (`IdTableRel.bound` makes it fire on the same
indices), the parent read, the intern, the table insert.

`sorry`: two arms over `Bridge/StoreNested.lean`'s `EStore.internName` spec
and `IdTableRel.insert`.  Task #97-P3-Frontend's sorry list, item 5. -/
theorem parseNameEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.NameRec}
    (hrun : parseNameEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseNameEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:240 parseLevelEntryD — a level
entry: four arms, each one `internLNode`.

`sorry`: `Bridge/Specs.lean`'s `internLNode_spec` at four constructors plus
`StateD_level_run` and `StateD_name_run` for the children.  Task
#97-P3-Frontend's sorry list, item 5. -/
theorem parseLevelEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.LevelRec}
    (hrun : parseLevelEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseLevelEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:259 parseExprEntryD — **the
expression entry, and the tier's real work**: ten constructors, each resolving
its children through the three tables and interning one node.  This is where
DESIGN §8.3's "the export's sharing is preserved exactly (lesson 25)" becomes
a theorem: the table hit is the same shared node on both sides, so the
denotation of the interned handle is con-leche's own `Expr` with con-leche's
own sharing.

`sorry`: ten arms over `Bridge/Specs.lean`'s ten `internE` faces and
`parsePwD_run`; the `lam`/`forallE` arms go through `internBindIE_spec'`
(`Bridge/StoreBind.lean`, with `Bridge/StoreBM.lean`'s `mi.tag = 0` supplied
by `pushBM`).  Task #97-P3-Frontend's sorry list, item 5. -/
theorem parseExprEntryD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {i : Nat} {r : ConLeche.Frontend.ExprRec}
    (hrun : parseExprEntryD sd i r s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.parseExprEntryD sc i r = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:192-194 parsePwD — the `pw`
datum.  The twin resolves the handles and READS THEM BACK (`PropWhen` holds
`ConLeche.Name`s, which the binder node carries as values), so the answer is
literally con-leche's and the theorem is an equation, not a relation.

`sorry`: `StateD_name_run` at the list, then `readName`'s exactness
(`Bridge/Specs.lean`).  Task #97-P3-Frontend's sorry list, item 5. -/
theorem parsePwD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {r : ConLeche.Frontend.PwRec} {pw : PropWhen}
    (hrun : parsePwD sd r s = .ok (pw, s')) :
    s' = s ∧ ConLeche.Frontend.parsePwD sc r = .ok pw := by
  sorry

/-! ## The declaration records -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:284 parseCVD — a constant's
header: a name, a level-parameter list and a type.

`sorry`: three reads plus `denoteNList`'s list induction.  Task
#97-P3-Frontend's sorry list, item 5. -/
theorem parseCVD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {cvr : ConLeche.Frontend.CVRec} {cv : IConstantVal}
    (hrun : parseCVD sd cvr s = .ok (cv, s')) :
    s' = s ∧ ∃ c, ConLeche.Frontend.parseCVD sc cvr = .ok c ∧
      denoteCV s.store cv = some c := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:137-153 noteDecl — the
declaration table, updated.  con-leche's is PURE and the twin's is monadic
only because `.basisDecl` fails loudly (`Arena/Frontend/ExportC.lean`'s own
note: no frontend function produces one), so the theorem is an equation at the
two maps.

`sorry`: `MapRel.insert` at `constTypes` and `heights`, six arms.  Task
#97-P3-Frontend's sorry list, item 6. -/
theorem noteDecl_run {s s' : AState} (hok : StateOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {d : IDeclaration} {dP : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : noteDecl sd d s = .ok (sd', s')) :
    s' = s ∧ StateDRel s.store sd' (ConLeche.Frontend.noteDecl sc dP) := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:161 pushDecl — the record
appended, then noted. -/
theorem pushDecl_run {s s' : AState} (hok : StateOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {d : IDeclaration} {dP : Declaration}
    (hpd : PersDecl d) (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : pushDecl sd d s = .ok (sd', s')) :
    s' = s ∧ PersStateD sd' ∧
      StateDRel s.store sd' (ConLeche.Frontend.pushDecl sc dP) := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:347 parseRuleD — one recursor
rule.

`sorry`: `StateD_name_run` and `getDeclD_run`.  Task #97-P3-Frontend's sorry
list, item 6. -/
theorem parseRuleD_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {ru : ConLeche.Frontend.RuleRec} {rl : IRecRule}
    (hrun : parseRuleD sd ru s = .ok (rl, s')) :
    s' = s ∧ ∃ r, ConLeche.Frontend.parseRuleD sc ru = .ok r ∧
      denoteRule s.store rl = some r := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:353-354 blockRecOf — the parsed
block, resolved, which is what the modeller seam is handed.

`sorry`: `parseCVD_run` and `parseRuleD_run` at three lists, then
`BlockRecRel`'s three `Forall₂`s.  Task #97-P3-Frontend's sorry list, item
6. -/
theorem blockRecOf_run {s s' : AState} (hok : StateOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {b : BlockRec}
    (hrun : blockRecOf sd tys cts rcs s = .ok (b, s')) :
    s' = s ∧ ∃ bP, ConLeche.Frontend.blockRecOf sc tys cts rcs = .ok bP ∧
      BlockRecRel s.store b bP := by
  sorry

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

`sorry`: `parseExprEntryD_run` / `parseNameEntryD_run` / `parseLevelEntryD_run`
/ `applyDeclD_run` and two `rfl`s.  Task #97-P3-Frontend's sorry list, item
9. -/
theorem applyLine_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {r : ConLeche.Frontend.LineRec}
    {x : StateD ⊕ RecordVerdict}
    (hrun : applyLine md sd r s = .ok (x, s')) :
    ParseStep s s' ∧ (∀ sd', x = .inl sd' → PersStateD sd') ∧
      ∃ y, ConLeche.Frontend.applyLine sc r = .ok y ∧ SumRel s'.store x y := by
  sorry

end ConRon.Bridge.Frontend

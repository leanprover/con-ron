/-
# `ConRon.Bridge.Frontend.Olean.EmitRec` — the emitter's records, on the denotations

The twin's emitter holds handles in its two tables and its records are upstream's own syntax,
indices into those tables.  So its relation to upstream's (`EmitRel`) is the tables' denotation
and the records' equality: a table's size is its image's, so an index is the same index.
-/
module

public import ConRon.Arena.Frontend.Olean.Emit
public import ConRon.Bridge.Frontend.Olean.MergeAll
public import ConLeche.Frontend.Olean.Emit

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry Emit entriesOf)
open ConLeche.Frontend (DeclRec CVRec IndTypeRec IndCtorRec IndRecRec RuleRec)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left)

/-- The expression relation. -/
abbrev ER (st : EStore) : EIdx → Expr → Prop := fun h e => denoteE st h = some e

/-- A constant against upstream's, read back. -/
abbrev CR (st : EStore) : CEntry → ConLeche.Frontend.Olean.CEntry → Prop :=
  fun c z => denoteCEntry st c = some z

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:30-36 Emit — **the emitter against upstream's**:
the tables denote, the records are the same. -/
structure EmitRel (st : EStore) (em : Emit) (emC : ConLeche.Frontend.Olean.Emit) : Prop where
  visited : SetRel st em.visited emC.visited
  names : ListRel (NR st) em.names.toList emC.names.toList
  exprs : ListRel (ER st) em.exprs.toList emC.exprs.toList
  out : em.out = emC.out

theorem EmitRel.empty (st : EStore) : EmitRel st {} {} :=
  ⟨SetRel.empty st, .nil, .nil, rfl⟩

theorem array_size_of_rel {α β : Type} {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ListRel R a.toList b.toList) : a.size = b.size := by
  have := h.length_eq
  simpa using this

theorem EmitRel.name {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {n : NIdx} {nC : ConLeche.Name} (hn : denoteN st.ns n = some nC) :
    EmitRel st (em.name n).1 (emC.name nC).1 ∧ (em.name n).2 = (emC.name nC).2 := by
  refine ⟨⟨h.visited, ?_, h.exprs, h.out⟩, array_size_of_rel h.names⟩
  simp only [Emit.name, ConLeche.Frontend.Olean.Emit.name, Array.toList_push]
  exact ListRel.append h.names (.cons hn .nil)

theorem EmitRel.expr {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {e : EIdx} {eC : Expr} (he : denoteE st e = some eC) :
    EmitRel st (em.expr e).1 (emC.expr eC).1 ∧ (em.expr e).2 = (emC.expr eC).2 := by
  refine ⟨⟨h.visited, h.names, ?_, h.out⟩, array_size_of_rel h.exprs⟩
  simp only [Emit.expr, ConLeche.Frontend.Olean.Emit.expr, Array.toList_push]
  exact ListRel.append h.exprs (.cons he .nil)

theorem EmitRel.push {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) (d : DeclRec) : EmitRel st (em.push d) (emC.push d) :=
  ⟨h.visited, h.names, h.exprs, by simp only [Emit.push, ConLeche.Frontend.Olean.Emit.push, h.out]⟩

theorem EmitRel.mark {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {n : NIdx} {nC : ConLeche.Name} (hn : denoteN st.ns n = some nC) :
    EmitRel st (em.mark n) (emC.mark nC) :=
  ⟨h.visited.insert hn, h.names, h.exprs, h.out⟩

/-- A list of names, emitted. -/
theorem names_fold {st : EStore} :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name}, ListRel (NR st) ns nsC →
      ∀ (em : Emit) (emC : ConLeche.Frontend.Olean.Emit) (acc : Array Nat), EmitRel st em emC →
      let x := ns.foldl (fun (y : Emit × Array Nat) p =>
        let (st, acc) := y
        let (st, i) := st.name p
        (st, acc.push i)) (em, acc)
      let xC := nsC.foldl (fun (y : ConLeche.Frontend.Olean.Emit × Array Nat) p =>
        let (st, acc) := y
        let (st, i) := st.name p
        (st, acc.push i)) (emC, acc)
      EmitRel st x.1 xC.1 ∧ x.2 = xC.2
  | _, _, .nil, _, _, _, h => ⟨h, rfl⟩
  | _, _, @ListRel.cons _ _ _ n nC ns nsC hn hr, em, emC, acc, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := h.name hn
    rw [h2]
    exact names_fold hr _ _ _ h1

theorem EmitRel.names' {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {ns : List NIdx} {nsC : List ConLeche.Name} (hr : ListRel (NR st) ns nsC) :
    EmitRel st (em.names' ns).1 (emC.names' nsC).1 ∧ (em.names' ns).2 = (emC.names' nsC).2 := by
  obtain ⟨h1, h2⟩ := names_fold hr em emC #[] h
  refine ⟨h1, ?_⟩
  simp only [Emit.names', ConLeche.Frontend.Olean.Emit.names']
  rw [show _ = _ from h2]

theorem EmitRel.cv {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {c : CEntry} {z : ConLeche.Frontend.Olean.CEntry} (hc : CR st c z) :
    EmitRel st (em.cv c).1 (emC.cv z).1 ∧ (em.cv c).2 = (emC.cv z).2 := by
  obtain ⟨hn, hl, ht, -⟩ := denoteCEntry_parts hc
  obtain ⟨h1, e1⟩ := h.name hn
  obtain ⟨h2, e2⟩ := h1.names' (listRel_of_mapM hl)
  obtain ⟨h3, e3⟩ := h2.expr ht
  have ea : em.cv c =
      (((((em.name c.c.name).1.names' c.c.levelParams).1).expr c.c.type).1,
       ⟨(em.name c.c.name).2, ((em.name c.c.name).1.names' c.c.levelParams).2,
        (((em.name c.c.name).1.names' c.c.levelParams).1.expr c.c.type).2⟩) := rfl
  have eb : emC.cv z =
      (((((emC.name z.name).1.names' z.levelParams).1).expr z.type).1,
       ⟨(emC.name z.name).2, ((emC.name z.name).1.names' z.levelParams).2,
        (((emC.name z.name).1.names' z.levelParams).1.expr z.type).2⟩) := rfl
  rw [ea, eb]
  exact ⟨h3, by simp only [e1, e2, e3]⟩

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:72-84 Emit.one -/
theorem EmitRel.one {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {c : CEntry} {z : ConLeche.Frontend.Olean.CEntry} (hc : CR st c z) :
    EmitRel st (em.one c) (emC.one z) := by
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hc
  obtain ⟨h1, e1⟩ := h.cv hc
  have ea : ∀ (y : Emit × CVRec), em.cv c = y → em.one c =
      (match c.c.kind with
        | .ax u => y.1.push (.ax y.2 u)
        | .defn v h s => (y.1.expr v).1.push (.defn y.2 (y.1.expr v).2 h s)
        | .thm v _ => (y.1.expr v).1.push (.thm y.2 (y.1.expr v).2)
        | .opaq v u => (y.1.expr v).1.push (.opaq y.2 (y.1.expr v).2 u)
        | .quot k => y.1.push (.quot y.2 k)
        | _ => y.1) := by
    intro y hy
    unfold Emit.one
    rw [hy]
    cases c.c.kind <;> rfl
  have eb : ∀ (y : ConLeche.Frontend.Olean.Emit × CVRec), emC.cv z = y → emC.one z =
      (match z.kind with
        | .ax u => y.1.push (.ax y.2 u)
        | .defn v h s => (y.1.expr v).1.push (.defn y.2 (y.1.expr v).2 h s)
        | .thm v _ => (y.1.expr v).1.push (.thm y.2 (y.1.expr v).2)
        | .opaq v u => (y.1.expr v).1.push (.opaq y.2 (y.1.expr v).2 u)
        | .quot k => y.1.push (.quot y.2 k)
        | _ => y.1) := by
    intro y hy
    unfold ConLeche.Frontend.Olean.Emit.one
    rw [hy]
    cases z.kind <;> rfl
  rw [ea _ rfl, eb _ rfl, ← e1]
  cases hk1 : c.c.kind with
  | ax u =>
    rw [hk1] at hk
    simp only [CKindF.mapM, pure, Option.some.injEq] at hk
    simp only [← hk]
    exact h1.push _
  | quot u =>
    rw [hk1] at hk
    simp only [CKindF.mapM, pure, Option.some.injEq] at hk
    simp only [← hk]
    exact h1.push _
  | defn v hs sf =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨w, hw, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    obtain ⟨h2, e2⟩ := h1.expr hw
    rw [← e2]
    exact h2.push _
  | thm v a =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨w, hw, hk⟩ := bind_some_left hk
    obtain ⟨as, -, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    obtain ⟨h2, e2⟩ := h1.expr hw
    rw [← e2]
    exact h2.push _
  | opaq v u =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨w, hw, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    obtain ⟨h2, e2⟩ := h1.expr hw
    rw [← e2]
    exact h2.push _
  | induct np ni all cs nn ir iu irf =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨as, -, hk⟩ := bind_some_left hk
    obtain ⟨cs', -, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    exact h1
  | ctor ind ci np nf iu =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨i', -, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    exact h1
  | recur all np ni nmo nmi rules kk iu =>
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨as, -, hk⟩ := bind_some_left hk
    obtain ⟨rs, -, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    simp only [← hk]
    exact h1

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:86-95 Emit.tyStep -/
theorem EmitRel.tyStep {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) (acc : Array IndTypeRec) {c : CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (hc : CR st c z) :
    EmitRel st (Emit.tyStep (em, acc) c).1 (ConLeche.Frontend.Olean.Emit.tyStep (emC, acc) z).1 ∧
      (Emit.tyStep (em, acc) c).2 = (ConLeche.Frontend.Olean.Emit.tyStep (emC, acc) z).2 := by
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hc
  obtain ⟨h1, e1⟩ := h.cv hc
  unfold Emit.tyStep ConLeche.Frontend.Olean.Emit.tyStep
  simp only []
  have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
  split
  · rename_i np ni al cs nn ir iu irf hk1
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨as, -, hk⟩ := bind_some_left hk
    obtain ⟨cs', hcs, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    rw [← hk]
    obtain ⟨h2, e2⟩ := h1.names' (listRel_of_mapM hcs)
    exact ⟨h2, by
      show acc.push _ = acc.push _
      simp only [e1, e2]⟩
  · rename_i hne
    have : ∀ np ni all cs nn ir iu irf, z.kind ≠ CKindF.induct np ni all cs nn ir iu irf := by
      intro np ni all cs nn ir iu irf hz
      rw [hz] at htag
      cases hk1 : c.c.kind <;> simp [hk1, CKindF.tag] at htag
      exact hne _ _ _ _ _ _ _ _ hk1
    split
    · rename_i hz
      exact absurd hz (this _ _ _ _ _ _ _ _)
    · exact ⟨h, rfl⟩

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:97-106 Emit.ctorStep -/
theorem EmitRel.ctorStep {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) (acc : Array IndCtorRec) {c : CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (hc : CR st c z) :
    EmitRel st (Emit.ctorStep (em, acc) c).1 (ConLeche.Frontend.Olean.Emit.ctorStep (emC, acc) z).1 ∧
      (Emit.ctorStep (em, acc) c).2 = (ConLeche.Frontend.Olean.Emit.ctorStep (emC, acc) z).2 := by
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hc
  obtain ⟨h1, e1⟩ := h.cv hc
  unfold Emit.ctorStep ConLeche.Frontend.Olean.Emit.ctorStep
  simp only []
  have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
  split
  · rename_i ind ci np nf iu hk1
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨i', hi, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    rw [← hk]
    obtain ⟨h2, e2⟩ := h1.name hi
    exact ⟨h2, by
      show acc.push _ = acc.push _
      simp only [e1, e2]⟩
  · rename_i hne
    have : ∀ ind ci np nf iu, z.kind ≠ CKindF.ctor ind ci np nf iu := by
      intro ind ci np nf iu hz
      rw [hz] at htag
      cases hk1 : c.c.kind <;> simp [hk1, CKindF.tag] at htag
      exact hne _ _ _ _ _ hk1
    split
    · rename_i hz
      exact absurd hz (this _ _ _ _ _)
    · exact ⟨h, rfl⟩

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:108-114 Emit.ruleStep — the rules of a
recursor, in order. -/
theorem rules_fold {st : EStore} :
    ∀ (rs : List (NIdx × Nat × EIdx)) {rsC : List (ConLeche.Name × Nat × Expr)},
      (rs.mapM fun (x : NIdx × Nat × EIdx) => do
          let c ← denoteN st.ns x.1
          let e ← denoteE st x.2.2
          pure (c, x.2.1, e)) = some rsC →
      ∀ (em : Emit) (emC : ConLeche.Frontend.Olean.Emit) (acc : Array RuleRec), EmitRel st em emC →
      EmitRel st (rs.foldl Emit.ruleStep (em, acc)).1
          (rsC.foldl ConLeche.Frontend.Olean.Emit.ruleStep (emC, acc)).1 ∧
        (rs.foldl Emit.ruleStep (em, acc)).2 = (rsC.foldl ConLeche.Frontend.Olean.Emit.ruleStep (emC, acc)).2
  | [], rsC, h, em, emC, acc, he => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨he, rfl⟩
  | ⟨cn, nf, rhs⟩ :: rs, rsC, h, em, emC, acc, he => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys, hys, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨a, ha, hy⟩ := bind_some_left hy
    obtain ⟨b, hb, hy⟩ := bind_some_left hy
    simp only [pure, Option.some.injEq] at hy
    subst hy
    simp only [List.foldl_cons]
    obtain ⟨h1, e1⟩ := he.name ha
    obtain ⟨h2, e2⟩ := h1.expr hb
    have e3 : Emit.ruleStep (em, acc) (cn, nf, rhs) =
        ((((em.name cn).1).expr rhs).1, acc.push (RuleRec.mk (em.name cn).2 nf (((em.name cn).1).expr rhs).2)) := rfl
    have e4 : ConLeche.Frontend.Olean.Emit.ruleStep (emC, acc) (a, nf, b) =
        ((((emC.name a).1).expr b).1, acc.push (RuleRec.mk (emC.name a).2 nf (((emC.name a).1).expr b).2)) := rfl
    rw [e3, e4, e1, e2]
    exact rules_fold rs hys _ _ _ h2

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:116-125 Emit.recStep -/
theorem EmitRel.recStep {st : EStore} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) (acc : Array IndRecRec) {c : CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (hc : CR st c z) :
    EmitRel st (Emit.recStep (em, acc) c).1 (ConLeche.Frontend.Olean.Emit.recStep (emC, acc) z).1 ∧
      (Emit.recStep (em, acc) c).2 = (ConLeche.Frontend.Olean.Emit.recStep (emC, acc) z).2 := by
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hc
  obtain ⟨h1, e1⟩ := h.cv hc
  unfold Emit.recStep ConLeche.Frontend.Olean.Emit.recStep
  simp only []
  have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
  split
  · rename_i al np ni nmo nmi rules kk iu hk1
    rw [hk1] at hk
    simp only [CKindF.mapM] at hk
    obtain ⟨as, -, hk⟩ := bind_some_left hk
    obtain ⟨rs, hrs, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    rw [← hk]
    obtain ⟨h2, e2⟩ := rules_fold rules hrs _ _ #[] h1
    exact ⟨h2, by
      show acc.push _ = acc.push _
      simp only [e1, e2]⟩
  · rename_i hne
    have : ∀ al np ni nmo nmi rules kk iu, z.kind ≠ CKindF.recur al np ni nmo nmi rules kk iu := by
      intro al np ni nmo nmi rules kk iu hz
      rw [hz] at htag
      cases hk1 : c.c.kind <;> simp [hk1, CKindF.tag] at htag
      exact hne _ _ _ _ _ _ _ _ hk1
    split
    · rename_i hz
      exact absurd hz (this _ _ _ _ _ _ _ _)
    · exact ⟨h, rfl⟩

/-- A fold over some constants of one of the block's three steps. -/
theorem steps_fold {st : EStore} {α : Type}
    {f : Emit × Array α → CEntry → Emit × Array α}
    {g : ConLeche.Frontend.Olean.Emit × Array α → ConLeche.Frontend.Olean.CEntry →
      ConLeche.Frontend.Olean.Emit × Array α}
    (hstep : ∀ {em : Emit} {emC : ConLeche.Frontend.Olean.Emit} (acc : Array α) {c z}, EmitRel st em emC →
      CR st c z → EmitRel st (f (em, acc) c).1 (g (emC, acc) z).1 ∧ (f (em, acc) c).2 = (g (emC, acc) z).2) :
    ∀ {cs : List CEntry} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (CR st) cs zs →
      ∀ (em : Emit) (emC : ConLeche.Frontend.Olean.Emit) (acc : Array α), EmitRel st em emC →
      EmitRel st (cs.foldl f (em, acc)).1 (zs.foldl g (emC, acc)).1 ∧
        (cs.foldl f (em, acc)).2 = (zs.foldl g (emC, acc)).2
  | _, _, .nil, _, _, _, h => ⟨h, rfl⟩
  | _, _, @ListRel.cons _ _ _ c z _ _ hc hr, em, emC, acc, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, e1⟩ := hstep acc h hc
    have e2 : f (em, acc) c = ((f (em, acc) c).1, (f (em, acc) c).2) := rfl
    have e3 : g (emC, acc) z = ((g (emC, acc) z).1, (g (emC, acc) z).2) := rfl
    rw [e2, e3, e1]
    exact steps_fold hstep hr _ _ _ h1

end ConRon.Bridge.Frontend.Olean

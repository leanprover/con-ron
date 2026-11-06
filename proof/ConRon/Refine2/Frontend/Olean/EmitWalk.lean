/-
# `ConRon.Refine2.Frontend.Olean.EmitWalk` — `olean/emit.rs`'s walk, against the twin's

**Task #142, Theorem 2.**  The Rust's stack is a `Vec` and its top, the twin's a `List` with the
head on top: `WorkStackRel`.  One popped item is one `workStep` of the twin, and the walk an
induction on the twin's fuel.  `PR` is the judgement of a Rust function that reads no state
against a twin action that leaves the state alone.
-/
import ConRon.Refine2.Frontend.Olean.Emit

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.emit (work_push push_uses push_uses_loop push_uses_named push_uses_of
  push_uses_of_loop push_visits push_visits_loop push_uses_block visit_step visit_named work_step
  emit_loop emit_loop_loop rec_map_add rec_map_all rec_map_all_loop rec_map_step rec_map_of
  rec_map_of_loop emit_all)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Arena.Frontend.Olean (Emit Work entriesOf blockTys blockCtors blockRecs quotConstants
  emitLoop recMapAdd recMapStep recMapOf emitAll outOfFuel)

/-! ## The stack -/

/-- A `Work` item, as the twin's. -/
def absWork : frontend.olean.emit.Work → Work
  | .Visit n => .visit (absNIdx n)
  | .One n => .one (absNIdx n)
  | .Quot cs => .quot (cs.val.map absNIdx)
  | .Block t c r => .block (t.val.map absNIdx) (c.val.map absNIdx) (r.val.map absNIdx)

/-- **The stack**: a `Vec` and its top, against a `List` with its head on top. -/
def WorkStackRel (stack : alloc.vec.Vec frontend.olean.emit.Work) (sp : Std.Usize)
    (l : List Work) : Prop :=
  sp.val ≤ stack.val.length ∧ (stack.val.take sp.val).reverse.map absWork = l

theorem take_set_succ {α : Type} : ∀ (l : List α) (i : Nat) (x : α), i < l.length →
    (l.set i x).take (i + 1) = l.take i ++ [x]
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, _ => by simp
  | a :: t, i + 1, x, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
    rw [take_set_succ t i x (by simpa using h)]

theorem work_vec_set_val (v : alloc.vec.Vec frontend.olean.emit.Work) (i : Std.Usize)
    (x : frontend.olean.emit.Work) : (alloc.vec.Vec.set v i x).val = v.val.set i.val x := by
  simp [alloc.vec.Vec.set_val_eq]

/-- **`work_push` is a cons.** -/
theorem work_push_rel {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {x : frontend.olean.emit.Work} {o}
    (h : work_push stack sp x = ok o) : WorkStackRel o.2 o.1 (absWork x :: l) := by
  rw [work_push] at h
  obtain ⟨hle, hl⟩ := hs
  peel h as stack1, h1
  peel h as i1, hi1
  cases Result.ok_injective h
  have hu := usize_succ hi1
  have hlen : (alloc.vec.Vec.len stack).val = stack.val.length := by simp [alloc.vec.Vec.len]
  split at h1
  · rename_i hlt
    have hlt' : sp.val < stack.val.length := by scalar_tac
    peel h1 as q, hq
    obtain ⟨w, back⟩ := q
    let _ : Inhabited frontend.olean.emit.Work := ⟨.Quot (alloc.vec.Vec.new _)⟩
    obtain ⟨-, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
    cases Result.ok_injective h1
    refine ⟨by simp; omega, ?_⟩
    show ((alloc.vec.Vec.set stack sp x).val.take i1.val).reverse.map absWork = _
    rw [work_vec_set_val, hu, take_set_succ _ _ _ hlt']
    simp [hl]
  · rename_i hge
    have heq : sp.val = stack.val.length := by scalar_tac
    have hv := ConRon.Refine.vec_push_val h1
    refine ⟨by rw [hv]; simp; omega, ?_⟩
    show (stack1.val.take i1.val).reverse.map absWork = _
    rw [hv, hu, heq]
    rw [heq, List.take_length] at hl
    simp [← hl]

theorem usize_pred {i i1 : Std.Usize} (h : i - 1#usize = ok i1) : i1.val + 1 = i.val := by
  have he := UScalar.sub_equiv i 1#usize
  rw [h] at he
  simp only [Result.match.ok] at he
  have hv : (1#usize).val = 1 := rfl
  have := he.2.1
  omega

/-- A pop. -/
theorem stack_pop {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp sp1 : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) (h1 : sp - 1#usize = ok sp1)
    {w : frontend.olean.emit.Work} {back} (w2 : frontend.olean.emit.Work)
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice frontend.olean.emit.Work)
      stack sp1 = ok (w, back)) :
    ∃ rest, l = absWork w :: rest ∧ sp1.val + 1 = sp.val ∧ WorkStackRel (back w2) sp1 rest := by
  let _ : Inhabited frontend.olean.emit.Work := ⟨.Quot (alloc.vec.Vec.new _)⟩
  obtain ⟨hlt, hw, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq h
  obtain ⟨hle, hl⟩ := hs
  have hsp := usize_pred h1
  refine ⟨(stack.val.take sp1.val).reverse.map absWork, ?_, hsp, ?_, ?_⟩
  · have hx : stack.val[sp1.val]? = some w := by rw [hw]; simp [hlt]
    rw [← hl, ← hsp, List.take_add_one, hx]
    simp
  · rw [work_vec_set_val]; simp; omega
  · rw [work_vec_set_val]
    rw [List.take_set_of_le (by omega)]

/-! ## A descending vector loop -/

/-- **A `Vec` loop from the top down, as a right fold**: what it pushes first ends up
deepest. -/
theorem down_loop {A S S' : Type} (v : alloc.vec.Vec A) {L : S → Std.Usize → Result S}
    {step : S → A → Result S}
    (hL : ∀ s i, L s i = if i > 0#usize then do
        let i1 ← i - 1#usize
        let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice A) v i1
        let s1 ← step s x
        L s1 i1
      else ok s)
    {Rel : S → S' → Prop} {f : A → S' → S'}
    (hstep : ∀ s y x s1, Rel s y → step s x = ok s1 → Rel s1 (f x y))
    {i : Std.Usize} {s : S} {y : S'} {r : S} (hs : Rel s y) (h : L s i = ok r) :
    Rel r ((v.val.take i.val).foldr f y) := by
  have key : ∀ (k : Nat) (i : Std.Usize) (s : S) (y : S'), i.val = k → Rel s y →
      L s i = ok r → Rel r ((v.val.take i.val).foldr f y) := by
    intro k
    induction k with
    | zero =>
      intro i s y hk hs h
      rw [hL, ite_eq_right (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [hk]
      exact hs
    | succ k ih =>
      intro i s y hk hs h
      rw [hL, ite_eq_left (by scalar_tac)] at h
      peel h as i1, hi1
      peel h as x, hx
      peel h as s1, hs1
      have hu := usize_pred hi1
      have e : v.val.take i.val = v.val.take i1.val ++ [x] := by
        rw [← hu, List.take_add_one, ConRon.Refine.ExprOps.vec_index_getElem? hx]
        rfl
      rw [e, List.foldr_append]
      exact ih i1 s1 _ (by omega) (hstep s y x s1 hs hs1) h
  exact key _ i s y rfl hs h

/-! ## Pushing visits -/

theorem foldr_cons_map {α β : Type} (g : α → β) (xs : List α) (l : List β) :
    xs.foldr (fun x y => g x :: y) l = xs.map g ++ l := by
  induction xs with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **Visits of some names, the first on top.** -/
theorem push_visits_rel {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_visits stack sp ns = ok o) :
    WorkStackRel o.2 o.1 (Work.visits (ns.val.map absNIdx) ++ l) := by
  rw [push_visits] at h
  have := down_loop (L := fun s i => push_visits_loop s.2 ns s.1 i) ns (s := (sp, stack)) (y := l)
    (step := fun s x => do
      let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x
      work_push s.2 s.1 (.Visit n1))
    (Rel := fun s l => WorkStackRel s.2 s.1 l) (f := fun x y => .visit (absNIdx x) :: y)
    (fun s i => by rw [push_visits_loop]; simp only [Std.bind_assoc]; rfl)
    (fun s y x s1 hs h1 => by
      peel h1 as n1, hn1
      rw [nidx_dup2_ok hn1] at h1
      exact work_push_rel hs h1) hs h
  rw [show (alloc.vec.Vec.len ns).val = ns.val.length by simp [alloc.vec.Vec.len], List.take_length,
    foldr_cons_map] at this
  simpa [Work.visits, Function.comp_def] using this

/-- **Visits of what one constant mentions.** -/
theorem push_uses_rel {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {c : frontend.olean.lazy.CEntry}
    {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c') {o}
    (h : push_uses stack sp c = ok o) :
    WorkStackRel o.2 o.1 (c'.uses.toList.map Work.visit ++ l) := by
  rw [push_uses] at h
  have := down_loop (L := fun s i => push_uses_loop s.2 c.uses s.1 i) c.uses (s := (sp, stack)) (y := l)
    (step := fun s x => do
      let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x
      work_push s.2 s.1 (.Visit n1))
    (Rel := fun s l => WorkStackRel s.2 s.1 l) (f := fun x y => .visit (absNIdx x) :: y)
    (fun s i => by rw [push_uses_loop]; simp only [Std.bind_assoc]; rfl)
    (fun s y x s1 hs h1 => by
      peel h1 as n1, hn1
      rw [nidx_dup2_ok hn1] at h1
      exact work_push_rel hs h1) hs h
  rw [show (alloc.vec.Vec.len c.uses).val = c.uses.val.length by simp [alloc.vec.Vec.len],
    List.take_length, foldr_cons_map] at this
  rw [← hc.2]
  simpa [Function.comp_def] using this

theorem usesOf_cons (mg' : Arena.Frontend.Olean.Merged) (a : NIdx) (t : List NIdx) :
    Work.usesOf mg' (a :: t) = Work.usesOf mg' [a] ++ Work.usesOf mg' t := by
  simp only [Work.usesOf, entriesOf, List.filterMap_cons, List.filterMap_nil]
  cases mg'.get a <;> simp

theorem usesOf_append (mg' : Arena.Frontend.Olean.Merged) (a t : List NIdx) :
    Work.usesOf mg' (a ++ t) = Work.usesOf mg' a ++ Work.usesOf mg' t := by
  simp [Work.usesOf, entriesOf, List.filterMap_append, List.flatMap_append]

theorem push_uses_named_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {n : arena.handle.NIdx} {o}
    (h : push_uses_named stack sp mg n = ok o) :
    WorkStackRel o.2 o.1 (Work.usesOf mg' [absNIdx n] ++ l) := by
  rw [push_uses_named] at h
  peel h as o1, h1
  have hr := mg_get_rel hm h1
  simp only [Work.usesOf, entriesOf, List.filterMap_cons, List.filterMap_nil]
  cases hg : mg'.get (absNIdx n) with
  | none =>
    rw [hg] at hr
    cases hr
    cases Result.ok_injective h
    simpa using hs
  | some c' =>
    rw [hg] at hr
    cases hr with
    | some hc => simpa using push_uses_rel hs hc h

theorem push_uses_of_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_uses_of stack sp mg ns = ok o) :
    WorkStackRel o.2 o.1 (Work.usesOf mg' (ns.val.map absNIdx) ++ l) := by
  rw [push_uses_of] at h
  have := down_loop (L := fun s i => push_uses_of_loop s.2 mg ns s.1 i) ns (s := (sp, stack)) (y := l)
    (step := fun s x => push_uses_named s.2 s.1 mg x)
    (Rel := fun s l => WorkStackRel s.2 s.1 l) (f := fun x y => Work.usesOf mg' [absNIdx x] ++ y)
    (fun s i => by rw [push_uses_of_loop]; rfl)
    (fun s y x s1 hs h1 => push_uses_named_rel hm hs h1) hs h
  rw [show (alloc.vec.Vec.len ns).val = ns.val.length by simp [alloc.vec.Vec.len],
    List.take_length] at this
  have e : ∀ xs : List arena.handle.NIdx,
      xs.foldr (fun x y => Work.usesOf mg' [absNIdx x] ++ y) l = Work.usesOf mg' (xs.map absNIdx) ++ l := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a t ih =>
      rw [List.foldr_cons, ih, List.map_cons, usesOf_cons mg' (absNIdx a) (t.map absNIdx), List.append_assoc]
  rwa [e] at this

theorem push_uses_block_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize}
    {l : List Work} (hs : WorkStackRel stack sp l) {tys ctors recs : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_uses_block stack sp mg tys ctors recs = ok o) :
    WorkStackRel o.2 o.1 (Work.usesOf mg' (tys.val.map absNIdx ++ ctors.val.map absNIdx ++ recs.val.map absNIdx) ++
      Work.block (tys.val.map absNIdx) (ctors.val.map absNIdx) (recs.val.map absNIdx) :: l) := by
  rw [push_uses_block] at h
  peel h as t2, ht2
  peel h as c2, hc2
  peel h as r2, hr2
  peel h as q1, h1
  obtain ⟨s1, st1⟩ := q1
  peel h as q2, h2
  obtain ⟨s2, st2⟩ := q2
  peel h as q3, h3
  obtain ⟨s3, st3⟩ := q3
  have a1 := work_push_rel hs h1
  have a2 := push_uses_of_rel hm a1 h2
  have a3 := push_uses_of_rel hm a2 h3
  have a4 := push_uses_of_rel hm a3 h
  rw [nidx_vec_dup_val ht2, nidx_vec_dup_val hc2, nidx_vec_dup_val hr2] at *
  rw [usesOf_append, usesOf_append, List.append_assoc, List.append_assoc]
  exact a4

/-! ## Marks -/

theorem mark_all_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {ns : alloc.vec.Vec arena.handle.NIdx} {st' : frontend.olean.emit.Emit}
    (h : frontend.olean.emit.mark_all st ns = ok st') :
    EmitRel st' ((ns.val.map absNIdx).foldl Emit.mark lst) := by
  rw [frontend.olean.emit.mark_all] at h
  have := up_loop (L := fun s i => frontend.olean.emit.mark_all_loop s ns i) ns
    (step := fun s x => frontend.olean.emit.emit_mark s x) (Rel := EmitRel)
    (f := fun y x => Emit.mark y (absNIdx x))
    (fun s i => by rw [frontend.olean.emit.mark_all_loop])
    (fun s y x s1 hs h1 => emit_mark_rel hs h1) hs h
  rw [foldl_map']
  exact this

/-! ## `skipped` -/

/-- **`c_entry_skipped` is `CEntry.skipped`.** -/
theorem c_entry_skipped_eq {c : frontend.olean.lazy.CEntry} {c' : Arena.Frontend.Olean.CEntry}
    (hc : CEntryRel c c') {b : Bool} (h : frontend.olean.closure.c_entry_skipped c = ok b) :
    b = c'.skipped := by
  rw [frontend.olean.closure.c_entry_skipped, frontend.olean.reads.c_kind_skipped.eq_def] at h
  have hk := hc.1.kind
  rw [Arena.Frontend.Olean.CEntry.skipped]
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try exact (hk : False).elim
  case Ax.ax u u' => cases (hk : u = u'); exact (Result.ok_injective h).symm
  case Defn.defn v hh s v' h' s' =>
    obtain ⟨-, -, rfl, hw⟩ := hk
    simp only [lift, bind_ok] at h
    peel h as b1, hb1
    cases Result.ok_injective h
    have hv : (Std.Array.to_slice frontend.olean.reads.c_kind_skipped.S_SAFE).val
        = [115#u32, 97#u32, 102#u32, 101#u32] := by
      unfold frontend.olean.reads.c_kind_skipped.S_SAFE; rfl
    have e := cps_beq_str hw (by rw [hv]; decide) hb1
    rw [hv] at e
    have e' : (b1 = true) ↔ ConRon.Refine.absString s = "safe" := e.trans (by rfl)
    show decide ¬ b1 = true = (ConRon.Refine.absString s != "safe")
    cases b1 <;> simp [e'.symm]
  case Thm.thm v a v' a' => exact (Result.ok_injective h).symm
  case Opaq.opaq v u v' u' =>
    obtain ⟨-, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Quot.quot s s' => exact (Result.ok_injective h).symm
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hk
    exact (Result.ok_injective h).symm
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨-, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm

/-! ## One step of the walk -/

/-- The twin's walk at a `visit` of a name stored and not filtered out: what it pushes. -/
def visitK (pk : Arena.Frontend.Olean.OleanPins) (mg : Arena.Frontend.Olean.Merged)
    (recMap : Std.HashMap NIdx (Array NIdx)) (n : NIdx) (k : ConLeche.Frontend.Olean.CKindF NIdx EIdx)
    (rest : List Work) (st : Emit) : List Work × Emit :=
  match k with
  | .ax _ | .defn .. | .thm .. | .opaq .. => (Work.usesOf mg [n] ++ Work.one n :: rest, st)
  | .quot _ =>
    let qs := quotConstants pk mg
    (Work.visit pk.nEq :: Work.quot qs :: rest, qs.foldl Emit.mark st)
  | .ctor ind .. => (Work.visit ind :: rest, st)
  | .recur all .. => (Work.visits all ++ rest, st)
  | .induct _ _ all _ _ _ _ _ =>
    let tys := blockTys mg all
    let ctors := blockCtors mg tys
    let recs := blockRecs mg recMap n
    (Work.usesOf mg (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest,
      (tys ++ ctors ++ recs).foldl Emit.mark st)

/-- **One popped item of the twin's walk.** -/
def workStep (pk : Arena.Frontend.Olean.OleanPins) (mg : Arena.Frontend.Olean.Merged)
    (recMap : Std.HashMap NIdx (Array NIdx)) (w : Work) (rest : List Work) (st : Emit) :
    List Work × Emit :=
  match w with
  | .one n => (rest, st.ones mg [n])
  | .quot cs => (rest, st.ones mg cs)
  | .block ts cs rs => (rest, st.block mg ts cs rs)
  | .visit n =>
    if st.visited.contains n then (rest, st) else
    match mg.get n with
    | none => (rest, st)
    | some c =>
      if c.skipped then (rest, st) else visitK pk mg recMap n c.c.kind rest (st.mark n)

theorem emitLoop_succ (pk : Arena.Frontend.Olean.OleanPins) (mg : Arena.Frontend.Olean.Merged)
    (recMap : Std.HashMap NIdx (Array NIdx)) (F : Nat) (w : Work) (rest : List Work) (st : Emit) :
    emitLoop pk mg recMap (F + 1) (w :: rest) st =
      emitLoop pk mg recMap F (workStep pk mg recMap w rest st).1 (workStep pk mg recMap w rest st).2 := by
  cases w with
  | one n => rw [emitLoop]; rfl
  | quot cs => rw [emitLoop]; rfl
  | block ts cs rs => rw [emitLoop]; rfl
  | visit n =>
    rw [emitLoop, workStep]
    by_cases h1 : st.visited.contains n = true
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      cases mg.get n with
      | none => rfl
      | some c =>
        dsimp only
        by_cases h2 : c.skipped = true
        · rw [ite_eq_left h2, ite_eq_left h2]
        · rw [ite_eq_right h2, ite_eq_right h2]
          cases c.c.kind <;> rfl

/-- `visit_step` at a constant that has a record of its own. -/
theorem visit_one {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize} {l : List Work}
    (hs : WorkStackRel stack sp l) {n : arena.handle.NIdx} {c : frontend.olean.lazy.CEntry}
    {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c') {lst1 : Emit}
    {st1 : frontend.olean.emit.Emit} (b1 : EmitRel st1 lst1) {o}
    (h : (do
      let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 n
      let (s, stack1) ← work_push stack sp (.One n1)
      let (i, stack2) ← push_uses stack1 s c
      ok (i, stack2, st1)) = ok o) :
    WorkStackRel o.2.1 o.1 (c'.uses.toList.map Work.visit ++ Work.one (absNIdx n) :: l) ∧
      EmitRel o.2.2 lst1 := by
  peel h as n1, hn1
  rw [nidx_dup2_ok hn1] at h
  peel h as p, hp
  obtain ⟨s, stack1⟩ := p
  peel h as q, hq
  obtain ⟨i, stack2⟩ := q
  cases Result.ok_injective h
  exact ⟨push_uses_rel (work_push_rel hs hp) hc hq, b1⟩

/-- **`visit_step` is `visitK`.** -/
theorem visit_step_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {rec_map rm} (hr : RecMapRel rec_map rm)
    {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize} {l : List Work}
    (hs : WorkStackRel stack sp l) {st : frontend.olean.emit.Emit} {lst : Emit} (he : EmitRel st lst)
    {n : arena.handle.NIdx} {c : frontend.olean.lazy.CEntry} {c' : Arena.Frontend.Olean.CEntry}
    (hc : CEntryRel c c') (hg : mg'.get (absNIdx n) = some c') {o}
    (h : visit_step pk mg rec_map stack sp st n c = ok o) :
    WorkStackRel o.2.1 o.1 (visitK (absPins pk) mg' rm (absNIdx n) c'.c.kind l (lst.mark (absNIdx n))).1 ∧
      EmitRel o.2.2 (visitK (absPins pk) mg' rm (absNIdx n) c'.c.kind l (lst.mark (absNIdx n))).2 := by
  rw [visit_step] at h
  peel h as st1, h1
  have b1 := emit_mark_rel he h1
  have hk := hc.1.kind
  have hu : Work.usesOf mg' [absNIdx n] = c'.uses.toList.map Work.visit := by
    simp [Work.usesOf, entriesOf, hg]
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try exact (hk : False).elim
  case Ax.ax u u' =>
    show WorkStackRel _ _ (Work.usesOf mg' [absNIdx n] ++ _) ∧ _
    rw [hu]
    exact visit_one hs hc b1 h
  case Defn.defn v hh s v' h' s' =>
    show WorkStackRel _ _ (Work.usesOf mg' [absNIdx n] ++ _) ∧ _
    rw [hu]
    exact visit_one hs hc b1 h
  case Thm.thm v a v' a' =>
    show WorkStackRel _ _ (Work.usesOf mg' [absNIdx n] ++ _) ∧ _
    rw [hu]
    exact visit_one hs hc b1 h
  case Opaq.opaq v u v' u' =>
    show WorkStackRel _ _ (Work.usesOf mg' [absNIdx n] ++ _) ∧ _
    rw [hu]
    exact visit_one hs hc b1 h
  case Quot.quot s s' =>
    peel h as qs, hqs
    peel h as st2, h2
    peel h as p, hp
    obtain ⟨s1, stack1⟩ := p
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    peel h as q, hq
    obtain ⟨i, stack2⟩ := q
    cases Result.ok_injective h
    have a2 := mark_all_rel b1 h2
    have a3 := work_push_rel (work_push_rel hs hp) hq
    rw [quot_constants_rel hm hqs] at a2
    refine ⟨?_, a2⟩
    have e : absWork (.Quot qs) = Work.quot (quotConstants (absPins pk) mg') := by
      rw [← quot_constants_rel hm hqs]; rfl
    rw [e] at a3
    exact a3
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨-, -, hall, -⟩ := hk
    have hall' : all.val.map absNIdx = all' := hall
    subst hall'
    peel h as tys, htys
    peel h as ctors, hctors
    peel h as recs, hrecs
    peel h as st2, h2
    peel h as st3, h3
    peel h as st4, h4
    peel h as q, hq
    obtain ⟨i, stack1⟩ := q
    cases Result.ok_injective h
    have a2 := mark_all_rel b1 h2
    have a3 := mark_all_rel a2 h3
    have a4 := mark_all_rel a3 h4
    have a5 := push_uses_block_rel hm hs hq
    have e1 := block_tys_rel hm htys
    have e2 := block_ctors_rel hm hctors
    have e3 := block_recs_rel hm hr hrecs
    rw [e2, e1, e3] at a5
    rw [← List.foldl_append, ← List.foldl_append, e2, e1, e3] at a4
    refine ⟨a5, ?_⟩
    show EmitRel _ (List.foldl Emit.mark _ (_ ++ _ ++ _))
    rw [List.append_assoc]
    exact a4
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨rfl, -⟩ := hk
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    peel h as q, hq
    obtain ⟨i, stack1⟩ := q
    cases Result.ok_injective h
    exact ⟨work_push_rel hs hq, b1⟩
  case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨hall, -⟩ := hk
    have hall' : all.val.map absNIdx = all' := hall
    subst hall'
    peel h as q, hq
    obtain ⟨i, stack1⟩ := q
    cases Result.ok_injective h
    exact ⟨push_visits_rel hs hq, b1⟩

/-- **`visit_named` is `workStep` at a `visit`.** -/
theorem visit_named_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {rec_map rm} (hr : RecMapRel rec_map rm)
    {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize} {l : List Work}
    (hs : WorkStackRel stack sp l) {st : frontend.olean.emit.Emit} {lst : Emit} (he : EmitRel st lst)
    {n : arena.handle.NIdx} {o}
    (h : visit_named pk mg rec_map stack sp st n = ok o) :
    WorkStackRel o.2.1 o.1 (workStep (absPins pk) mg' rm (.visit (absNIdx n)) l lst).1 ∧
      EmitRel o.2.2 (workStep (absPins pk) mg' rm (.visit (absNIdx n)) l lst).2 := by
  rw [visit_named] at h
  peel h as b, hb
  have hb' := ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 he.inv (anyNKeysOk _) trivial hb
  rw [he.visited n] at hb'
  rw [workStep, ← hb']
  cases b with
  | true =>
    cases Result.ok_injective h
    exact ⟨hs, he⟩
  | false =>
    rw [ite_eq_right (by simp)]
    peel h as o1, h1
    have hg := mg_get_rel hm h1
    cases hg' : mg'.get (absNIdx n) with
    | none =>
      rw [hg'] at hg
      cases hg
      cases Result.ok_injective h
      exact ⟨hs, he⟩
    | some c' =>
      rw [hg'] at hg
      cases hg with
      | some hc =>
        peel h as b1, hb1
        rw [c_entry_skipped_eq hc hb1] at h
        dsimp only
        cases hsk : c'.skipped with
        | true =>
          rw [hsk] at h
          cases Result.ok_injective h
          exact ⟨hs, he⟩
        | false =>
          rw [hsk] at h
          exact visit_step_rel hm hr hs he hc hg' h

/-- **`work_step` is `workStep`.** -/
theorem work_step_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {rec_map rm} (hr : RecMapRel rec_map rm)
    {stack : alloc.vec.Vec frontend.olean.emit.Work} {sp : Std.Usize} {l : List Work}
    (hs : WorkStackRel stack sp l) {st : frontend.olean.emit.Emit} {lst : Emit} (he : EmitRel st lst)
    {w : frontend.olean.emit.Work} {o} (h : work_step pk mg rec_map stack sp st w = ok o) :
    WorkStackRel o.2.1 o.1 (workStep (absPins pk) mg' rm (absWork w) l lst).1 ∧
      EmitRel o.2.2 (workStep (absPins pk) mg' rm (absWork w) l lst).2 := by
  unfold work_step at h
  cases w with
  | Visit n => exact visit_named_rel hm hr hs he h
  | One n =>
    peel h as st1, h1
    cases Result.ok_injective h
    exact ⟨hs, one_named_rel he hm h1⟩
  | Quot cs =>
    peel h as st1, h1
    cases Result.ok_injective h
    exact ⟨hs, emit_ones_rel he hm h1⟩
  | Block ts cs rs =>
    peel h as st1, h1
    cases Result.ok_injective h
    exact ⟨hs, emit_block_rel he hm h1⟩

/-! ## The walk -/

/-- What a Rust outcome claims of a twin run from `s`. -/
def POut {α β : Type} (R : α → β → Prop) (s : AState)
    (o : core.result.Result α kernel.core_types.CheckError)
    (y : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b, y = .ok (b, s) ∧ R a b
  | .Err e => AErrSim e y

/-- **The lockstep judgement of a function that reads no state**: the twin's action leaves any
state alone, and a Rust error is a twin failure of the kind. -/
def PR {α β : Type} (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError)) (x : AM β) : Prop :=
  ∀ o, m = ok o → ∀ s, POut R s o (x.run s)

theorem out_of_fuel_err {T : Type} {r} (h : frontend.olean.closure.out_of_fuel T = ok r) :
    ∃ v, r = .Err (.Internal v) := by
  rw [frontend.olean.closure.out_of_fuel] at h
  peel h as s, -
  peel h as v, -
  peel h as ce, hce
  rw [kernel.core_types.internal] at hce
  cases Result.ok_injective hce
  cases Result.ok_injective h
  exact ⟨_, rfl⟩

/-- **The walk**, by induction on the twin's fuel. -/
theorem emit_loop_loop_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {rec_map rm} (hr : RecMapRel rec_map rm)
    (F : Nat) : ∀ (fuel : Std.U64) (stack : alloc.vec.Vec frontend.olean.emit.Work) (sp : Std.Usize)
      (l : List Work) (st : frontend.olean.emit.Emit) (lst : Emit) (r stack' st'),
      fuel.val = F → WorkStackRel stack sp l → EmitRel st lst →
      emit_loop_loop pk mg rec_map stack st sp fuel = ok (r, stack', st') → ∀ s,
        POut (fun _ le => EmitRel st' le) s r ((emitLoop (absPins pk) mg' rm F l lst).run s) := by
  have hstop : ∀ (F : Nat) (fuel : Std.U64) (stack : alloc.vec.Vec frontend.olean.emit.Work)
      (sp : Std.Usize) (l : List Work) (st : frontend.olean.emit.Emit) (lst : Emit) (r stack' st') s,
      sp.val = 0 → WorkStackRel stack sp l → EmitRel st lst →
      emit_loop_loop pk mg rec_map stack st sp fuel = ok (r, stack', st') →
      POut (fun _ le => EmitRel st' le) s r ((emitLoop (absPins pk) mg' rm F l lst).run s) := by
    intro F fuel stack sp l st lst r stack' st' s hsp hs he h
    rw [emit_loop_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    have hl : l = [] := by rw [← hs.2, hsp]; rfl
    subst hl
    refine ⟨lst, ?_, he⟩
    cases F <;> rfl
  induction F with
  | zero =>
    intro fuel stack sp l st lst r stack' st' hf hs he h s
    by_cases hsp : sp.val = 0
    · exact hstop _ _ _ _ _ _ _ _ _ _ _ hsp hs he h
    · rw [emit_loop_loop, ite_eq_left (by scalar_tac), ite_eq_left (by scalar_tac)] at h
      peel h as r1, hr1
      obtain ⟨v, rfl⟩ := out_of_fuel_err hr1
      cases Result.ok_injective h
      have hlen : l.length = sp.val := by
        have e := congrArg List.length hs.2
        simp at e
        have := hs.1
        omega
      cases l with
      | nil => exact absurd hlen.symm (by simpa using hsp)
      | cons w rest =>
        intro k hk
        cases hk
        exact ⟨_, rfl, rfl⟩
  | succ F ih =>
    intro fuel stack sp l st lst r stack' st' hf hs he h s
    by_cases hsp : sp.val = 0
    · exact hstop _ _ _ _ _ _ _ _ _ _ _ hsp hs he h
    · rw [emit_loop_loop, ite_eq_left (by scalar_tac), ite_eq_right (by scalar_tac)] at h
      peel h as fuel1, hf1
      peel h as sp1, hsp1
      peel h as q, hq
      obtain ⟨w, back⟩ := q
      peel h as n, -
      obtain ⟨rest, rfl, -, hs1⟩ := stack_pop hs hsp1 (.Visit n) hq
      peel h as p, hp
      obtain ⟨sp2, stack2, st1⟩ := p
      obtain ⟨a, b⟩ := work_step_rel hm hr hs1 he hp
      rw [emitLoop_succ]
      exact ih fuel1 stack2 sp2 _ st1 _ r stack' st' (by rw [fuel_pred hf1, hf]; rfl) a b h s

/-! ## The recursors' map -/

theorem nidx_contains_from (ns : alloc.vec.Vec arena.handle.NIdx) (n : arena.handle.NIdx) (k : Nat) :
    ∀ (i : Std.Usize) (o : Bool), ns.val.length - i.val = k →
      arena.env.nidx_vec_contains_from ns i n = ok o →
      o = ((ns.val.drop i.val).map absNIdx).contains (absNIdx n) := by
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.env.nidx_vec_contains_from, ite_eq_left (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [drop_stop hk]; rfl
  | succ k ih =>
    intro i o hk h
    rw [arena.env.nidx_vec_contains_from, ite_eq_right (by scalar_tac)] at h
    peel h as n1, hn1
    peel h as b, hb
    rw [idx_cons hn1, List.map_cons, List.contains_cons, BEq.comm, ← nidx_eq2_abs hb]
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h
      exact (Result.ok_injective h).symm
    | false =>
      rw [ite_eq_right (by simp)] at h
      peel h as i2, hi2
      rw [Bool.false_or, ← usize_succ hi2]
      exact ih i2 o (by rw [usize_succ hi2]; omega) h

theorem nidx_contains_eq {ns : alloc.vec.Vec arena.handle.NIdx} {n : arena.handle.NIdx} {o : Bool}
    (h : arena.env.nidx_vec_contains ns n = ok o) :
    o = (ns.val.map absNIdx).contains (absNIdx n) := by
  rw [arena.env.nidx_vec_contains] at h
  exact nidx_contains_from ns n _ 0#usize o rfl h

/-- A member of the map, taken out and put back with a new value: `alter`. -/
theorem rec_replace {m m1 m2 : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec arena.handle.NIdx)}
    {m' : Std.HashMap NIdx (Array NIdx)} (hr : RecMapRel m m') {i : arena.handle.NIdx} {o old a}
    {f : Option (Array NIdx) → Option (Array NIdx)}
    (rem : ron.hashmap2.HashMap2.remove arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 m i = ok (o, m1))
    (ins : ron.hashmap2.HashMap2.insert arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 m1 i a = ok (old, m2))
    (e : f (o.map fun v => (v.val.map absNIdx).toArray) = some (a.val.map absNIdx).toArray) :
    RecMapRel m2 (m'.alter (absNIdx i) f) := by
  obtain ⟨hi1, ho, hu1, hk1⟩ := ConRon.Refine.HashMap2.remove_refines_gen nidx_eq2 hr.inv (anyNKeysOk _) trivial rem
  obtain ⟨hi2, -, hu2, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hi1 hk1 trivial ins
  refine ⟨fun k _ => ?_, hi2⟩
  rw [hu2, hu1, Function.update_apply, Function.update_apply, Std.HashMap.getElem?_alter]
  by_cases hk : k = i
  · subst hk
    simp only [ite_true, beq_self_eq_true]
    rw [← hr.map k trivial, ← ho, e]
    rfl
  · have hne : (absNIdx i == absNIdx k) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, ite_eq_right hk, hne]
    simpa using hr.map k trivial

/-- **`rec_map_add` is `recMapAdd`**: remove and insert, against `alter`. -/
theorem rec_map_add_rel {m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec arena.handle.NIdx)}
    {m' : Std.HashMap NIdx (Array NIdx)} (hr : RecMapRel m m') {n i : arena.handle.NIdx} {m2}
    (h : rec_map_add m n i = ok m2) : RecMapRel m2 (recMapAdd (absNIdx n) m' (absNIdx i)) := by
  rw [rec_map_add] at h
  peel h as q, hq
  obtain ⟨o, m1⟩ := q
  rw [recMapAdd]
  cases o with
  | none =>
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    peel h as a1, ha1
    peel h as n2, hn2
    rw [nidx_dup2_ok hn2] at h
    peel h as p, hp
    obtain ⟨old, m3⟩ := p
    cases Result.ok_injective h
    refine rec_replace hr hq hp ?_
    rw [ConRon.Refine.vec_push_val ha1]
    rfl
  | some a =>
    peel h as b, hb
    peel h as a1, ha1
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    peel h as p, hp
    obtain ⟨old, m3⟩ := p
    cases Result.ok_injective h
    refine rec_replace hr hq hp ?_
    have hc := nidx_contains_eq hb
    show some (if ((a.val.map absNIdx).toArray).contains (absNIdx n) then _ else _) = _
    rw [List.contains_toArray, ← hc]
    cases b with
    | true =>
      cases Result.ok_injective ha1
      rfl
    | false =>
      peel ha1 as n3, hn3
      rw [nidx_dup2_ok hn3] at ha1
      rw [ConRon.Refine.vec_push_val ha1]
      simp

theorem rec_map_step_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {m m'} (hr : RecMapRel m m') {n : arena.handle.NIdx} {m2}
    (h : rec_map_step mg m n = ok m2) : RecMapRel m2 (recMapStep mg' m' (absNIdx n)) := by
  rw [rec_map_step] at h
  peel h as o1, h1
  have hg := mg_get_rel hm h1
  rw [recMapStep]
  cases hg' : mg'.get (absNIdx n) with
  | none =>
    rw [hg'] at hg
    cases hg
    cases Result.ok_injective h
    exact hr
  | some c' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      have hk := hc.1.kind
      dsimp only [Option.map] at h ⊢
      generalize frontend.olean.spec.CEntryF.kind _ = k at h hk
      generalize c'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try first
        | exact (hk : False).elim
        | (cases Result.ok_injective h; exact hr)
      case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
        obtain ⟨hall, -⟩ := hk
        have hall' : all.val.map absNIdx = all' := hall
        subst hall'
        dsimp only at h
        rw [rec_map_all] at h
        have := up_loop (L := fun s i => rec_map_all_loop s n all i) all
          (step := fun s x => rec_map_add s n x) (Rel := RecMapRel)
          (f := fun y x => recMapAdd (absNIdx n) y (absNIdx x))
          (fun s i => by rw [rec_map_all_loop])
          (fun s y x s1 hs h1 => rec_map_add_rel hs h1) hr h
        show RecMapRel m2 (List.foldl (recMapAdd (absNIdx n)) m' (List.map absNIdx all.val))
        rw [foldl_map']
        exact this

/-- **`rec_map_of` is `recMapOf`.** -/
theorem rec_map_of_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {m2} (h : rec_map_of mg = ok m2) : RecMapRel m2 (recMapOf mg') := by
  rw [rec_map_of] at h
  peel h as m0, h0
  obtain ⟨hinv0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) h0
  have := up_loop (L := fun s i => rec_map_of_loop mg s i) mg.order
    (step := fun s x => rec_map_step mg s x) (Rel := RecMapRel) (y := {})
    (f := fun y x => recMapStep mg' y (absNIdx x))
    (fun s i => by rw [rec_map_of_loop])
    (fun s y x s1 hs h1 => rec_map_step_rel hm hs h1)
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv0⟩ h
  rw [recMapOf, ← Array.foldl_toList, ← hm.order, foldl_map']
  exact this

/-! ## The whole walk -/

/-- The Rust's new emitter against the twin's. -/
theorem emit_new_rel {hm : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    (h : ron.hashmap2.HashMap2.new arena.handle.NIdx Bool = ok hm) :
    EmitRel { visited := hm, names := alloc.vec.Vec.new _, exprs := alloc.vec.Vec.new _,
              out := alloc.vec.Vec.new _ } {} := by
  obtain ⟨hinv0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) h
  refine ⟨fun n => ?_, hinv0, rfl, rfl, rfl, fun d hd => ?_⟩
  · show (toFun hm n).isSome = (∅ : Std.HashSet NIdx).contains _
    rw [hnone n]; simp
  · exact absurd hd (by simp [alloc.vec.Vec.new])

/-- **`emit_all` is `emitAll`.** -/
theorem emit_all_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {roots : alloc.vec.Vec arena.handle.NIdx} {roots' : Array NIdx}
    (hroots : roots.val.map absNIdx = roots'.toList) :
    PR EmitRel (emit_all pk mg roots) (emitAll (absPins pk) mg' roots') := by
  intro o h s
  rw [emit_all] at h
  peel h as rm, hrm
  peel h as hm0, h0
  peel h as q, hq
  obtain ⟨top, stack⟩ := q
  peel h as p, hp
  obtain ⟨r, stack2, st⟩ := p
  rw [emit_loop] at hp
  peel hp as fuel, hf
  have hs0 : WorkStackRel (alloc.vec.Vec.with_capacity frontend.olean.emit.Work (alloc.vec.Vec.len roots))
      0#usize [] := ⟨by simp, rfl⟩
  have hs1 := push_visits_rel hs0 hq
  rw [hroots, List.append_nil] at hs1
  have := emit_loop_loop_rel hm (rec_map_of_rel hm hrm) _ fuel stack top _ _ {} r stack2 st
    (closure_fuel_val hf) hs1 (emit_new_rel h0) hp s
  cases r with
  | Ok u =>
    cases Result.ok_injective h
    exact this
  | Err e =>
    cases Result.ok_injective h
    exact this

end ConRon.Refine2.Frontend.Olean

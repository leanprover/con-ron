/-
# `ConRon.Refine2.Frontend.Olean.Emit` — `olean/emit.rs`'s records, against the twin's

**Task #142, Theorem 2.**  The emission is pure on the twin's side (`Emit.*` over `Emit`
values) and `&mut` on the Rust's.  `EmitRel` relates the two: the visited names as a set, by
membership, with the table's `Inv`; the tables and the record stream elementwise, and every
record's spellings well formed, which `process_line_core_d`'s refinement asks.  This file is
the records; `EmitWalk.lean` is the walk, `EmitBlocks.lean` the check of the blocks.
-/
import ConRon.Refine2.Frontend.Olean.Merge

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.emit (emit_name emit_expr emit_mark emit_names emit_names_loop emit_cv emit_one
  emit_ty_step emit_ctor_step emit_rule_step emit_rec_step emit_rec_step_loop ty_named ctor_named
  rec_named one_named emit_block emit_block_loop0 emit_block_loop1 emit_block_loop2 emit_ones
  emit_ones_loop mark_all mark_all_loop block_tys block_tys_loop push_stored push_stored_loop
  block_ctors_of block_ctors block_ctors_loop block_recs quot_names quot_constants)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Arena.Frontend.Olean (Emit entriesOf blockTys blockCtors blockRecs quotNames quotConstants)
open ConLeche.Frontend (IndTypeRec IndCtorRec IndRecRec RuleRec CVRec DeclRec)

/-- **`emit::Emit` against the twin's.** -/
structure EmitRel (st : frontend.olean.emit.Emit) (lst : Emit) : Prop where
  visited : ∀ n, (toFun st.visited n).isSome = lst.visited.contains (absNIdx n)
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable st.visited
  names : st.names.val.map absNIdx = lst.names.toList
  exprs : st.exprs.val.map absEIdx = lst.exprs.toList
  out : st.out.val.map absDeclRec = lst.out.toList
  wf : ∀ d ∈ st.out.val, DeclRecStrWF d

/-- An emitter and an accumulator of records. -/
def StAcc {T T' : Type} (A : T → T') (x : frontend.olean.emit.Emit × alloc.vec.Vec T)
    (y : Emit × Array T') : Prop :=
  EmitRel x.1 y.1 ∧ x.2.val.map A = y.2.toList

/-! ## Positions in a vector -/

theorem usize_succ {i i2 : Std.Usize} (h : i + 1#usize = ok i2) : i2.val = i.val + 1 := by
  have hu := ConRon.Refine.Nat.uadd_val h
  have h1 : (1#usize).val = 1 := rfl
  rwa [h1] at hu

theorem idx_cons {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val.drop i.val = x :: v.val.drop (i.val + 1) := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? h)
  rw [List.drop_eq_getElem_cons hl, e]

theorem drop_stop {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hk : v.val.length - i.val = 0) : v.val.drop i.val = [] :=
  List.drop_eq_nil_of_le (by omega)

/-- A `Vec` loop whose counter has run out. -/
theorem not_lt_len {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hk : v.val.length - i.val = 0) : ¬ i < alloc.vec.Vec.len v := by
  have : (alloc.vec.Vec.len v).val = v.val.length := by simp [alloc.vec.Vec.len]
  scalar_tac

/-- A `Vec` loop whose counter has not. -/
theorem lt_len {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {k : Nat}
    (hk : v.val.length - i.val = k + 1) : i < alloc.vec.Vec.len v := by
  have : (alloc.vec.Vec.len v).val = v.val.length := by simp [alloc.vec.Vec.len]
  scalar_tac

/-! ## The tables -/

theorem emit_name_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {n : arena.handle.NIdx} {o : Std.U64 × frontend.olean.emit.Emit} (h : emit_name st n = ok o) :
    EmitRel o.2 (lst.name (absNIdx n)).1 ∧ absU64 o.1 = (lst.name (absNIdx n)).2 := by
  rw [emit_name] at h
  peel h as i1, hi1
  peel h as n1, hn1
  peel h as v, hv
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn1] at hv
  refine ⟨⟨hs.visited, hs.inv, ?_, hs.exprs, hs.out, hs.wf⟩, ?_⟩
  · show (v.val.map absNIdx) = (lst.names.push (absNIdx n)).toList
    rw [ConRon.Refine.vec_push_val hv, List.map_append, hs.names]; simp
  · show i1.val = lst.names.size
    have := ConRon.Refine2.Frontend.cast_u64_usize hi1
    rw [this]
    have e := congrArg List.length hs.names
    simpa [alloc.vec.Vec.len] using e

theorem emit_expr_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {n : arena.handle.EIdx} {o : Std.U64 × frontend.olean.emit.Emit} (h : emit_expr st n = ok o) :
    EmitRel o.2 (lst.expr (absEIdx n)).1 ∧ absU64 o.1 = (lst.expr (absEIdx n)).2 := by
  rw [emit_expr] at h
  peel h as i1, hi1
  peel h as n1, hn1
  peel h as v, hv
  cases Result.ok_injective h
  rw [eidx_dup2_ok hn1] at hv
  refine ⟨⟨hs.visited, hs.inv, hs.names, ?_, hs.out, hs.wf⟩, ?_⟩
  · show (v.val.map absEIdx) = (lst.exprs.push (absEIdx n)).toList
    rw [ConRon.Refine.vec_push_val hv, List.map_append, hs.exprs]; simp
  · show i1.val = lst.exprs.size
    have := ConRon.Refine2.Frontend.cast_u64_usize hi1
    rw [this]
    have e := congrArg List.length hs.exprs
    simpa [alloc.vec.Vec.len] using e

/-- A visited set, one insert further. -/
theorem visited_insert {V : Type} {m m' : ron.hashmap2.HashMap2 arena.handle.NIdx V}
    {s : Std.HashSet NIdx} (hv : ∀ n, (toFun m n).isSome = s.contains (absNIdx n))
    (hinv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m)
    {n : arena.handle.NIdx} {x : V} {old}
    (h : ron.hashmap2.HashMap2.insert arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 m n x = ok (old, m')) :
    (∀ k, (toFun m' k).isSome = (s.insert (absNIdx n)).contains (absNIdx k)) ∧
      Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m' := by
  obtain ⟨h1, -, h2, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hinv (anyNKeysOk _) trivial h
  refine ⟨fun k => ?_, h1⟩
  rw [h2, Function.update_apply, Std.HashSet.contains_insert]
  by_cases hk : k = n
  · subst hk; simp
  · have hne : (absNIdx n == absNIdx k) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, hne, Bool.false_or, hv k]

theorem emit_mark_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {n : arena.handle.NIdx} {st' : frontend.olean.emit.Emit} (h : emit_mark st n = ok st') :
    EmitRel st' (lst.mark (absNIdx n)) := by
  rw [emit_mark] at h
  peel h as n1, hn1
  peel h as q, hq
  obtain ⟨old, m2⟩ := q
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn1] at hq
  obtain ⟨h1, h2⟩ := visited_insert hs.visited hs.inv hq
  exact ⟨h1, h2, hs.names, hs.exprs, hs.out, hs.wf⟩

/-- The step of the twin's `Emit.names'`. -/
def namesF : Emit × Array Nat → NIdx → Emit × Array Nat :=
  fun (st, acc) p => let (st, i) := st.name p; (st, acc.push i)

theorem emit_names_loop_rel (ns : alloc.vec.Vec arena.handle.NIdx) (k : Nat) :
    ∀ (st : frontend.olean.emit.Emit) (lst : Emit) (acc : alloc.vec.Vec Std.U64) (lacc : Array Nat)
      (i : Std.Usize) (o), EmitRel st lst → acc.val.map absU64 = lacc.toList →
      ns.val.length - i.val = k → emit_names_loop st ns acc i = ok o →
      o.1.val.map absU64 = (((ns.val.drop i.val).map absNIdx).foldl namesF (lst, lacc)).2.toList ∧
        EmitRel o.2 (((ns.val.drop i.val).map absNIdx).foldl namesF (lst, lacc)).1 := by
  induction k with
  | zero =>
    intro st lst acc lacc i o hs ha hk h
    rw [emit_names_loop, ite_eq_right (not_lt_len hk)] at h
    cases Result.ok_injective h
    rw [drop_stop hk]
    exact ⟨ha, hs⟩
  | succ k ih =>
    intro st lst acc lacc i o hs ha hk h
    rw [emit_names_loop, ite_eq_left (lt_len hk)] at h
    peel h as n, hn
    peel h as q, hq
    obtain ⟨i2, st1⟩ := q
    peel h as acc1, hacc
    peel h as i3, hi3
    obtain ⟨h1, h2⟩ := emit_name_rel hs hq
    rw [idx_cons hn, List.map_cons, List.foldl_cons, ← usize_succ hi3]
    refine ih st1 _ acc1 _ i3 o h1 ?_ (by rw [usize_succ hi3]; omega) h
    rw [ConRon.Refine.vec_push_val hacc, List.map_append, ha]
    simp only [List.map_cons, List.map_nil]
    rw [h2]
    simp only [Array.toList_push]
    rfl



theorem emit_names_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {ns : alloc.vec.Vec arena.handle.NIdx} {o} (h : emit_names st ns = ok o) :
    absU64s o.1 = (lst.names' (ns.val.map absNIdx)).2 ∧
      EmitRel o.2 (lst.names' (ns.val.map absNIdx)).1 := by
  rw [emit_names] at h
  exact emit_names_loop_rel ns _ st lst _ #[] 0#usize o hs rfl rfl h

theorem emit_cv_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {c : frontend.olean.closure.CEntry} {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c')
    {o} (h : emit_cv st c = ok o) :
    absCVRec o.1 = (lst.cv c').2 ∧ EmitRel o.2 (lst.cv c').1 := by
  rw [emit_cv] at h
  peel h as q1, h1
  obtain ⟨n, st1⟩ := q1
  peel h as q2, h2
  obtain ⟨lps, st2⟩ := q2
  peel h as q3, h3
  obtain ⟨t, st3⟩ := q3
  cases Result.ok_injective h
  obtain ⟨a1, b1⟩ := emit_name_rel hs h1
  obtain ⟨a2, b2⟩ := emit_names_rel a1 h2
  obtain ⟨a3, b3⟩ := emit_expr_rel b2 h3
  have e1 := hc.1.«name»
  have e2 : c.c.level_params.val.map absNIdx = c'.c.levelParams := hc.1.levelParams
  have e3 := hc.1.type
  rw [e1] at a1 b1
  rw [e1, e2] at a2 b2
  rw [e1, e2, e3] at a3 b3
  refine ⟨?_, a3⟩
  exact congr (congr (congrArg CVRec.mk b1) a2) b3

/-! ## A vector loop -/

/-- **A `Vec` loop, as a fold**: `L` steps over `v` from a position, `step` is its body, and a
relation carried across the body is carried across the loop. -/
theorem up_loop {A S S' : Type} (v : alloc.vec.Vec A) {L : S → Std.Usize → Result S}
    {step : S → A → Result S}
    (hL : ∀ s i, L s i = if i < alloc.vec.Vec.len v then do
        let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice A) v i
        let s1 ← step s x
        let i2 ← i + 1#usize
        L s1 i2
      else ok s)
    {Rel : S → S' → Prop} {f : S' → A → S'}
    (hstep : ∀ s y x s1, Rel s y → step s x = ok s1 → Rel s1 (f y x))
    {i : Std.Usize} {s : S} {y : S'} {r : S} (hs : Rel s y) (h : L s i = ok r) :
    Rel r ((v.val.drop i.val).foldl f y) := by
  have key : ∀ (k : Nat) (i : Std.Usize) (s : S) (y : S'), v.val.length - i.val = k → Rel s y →
      L s i = ok r → Rel r ((v.val.drop i.val).foldl f y) := by
    intro k
    induction k with
    | zero =>
      intro i s y hk hs h
      rw [hL, ite_eq_right (not_lt_len hk)] at h
      cases Result.ok_injective h
      rw [drop_stop hk]
      exact hs
    | succ k ih =>
      intro i s y hk hs h
      rw [hL, ite_eq_left (lt_len hk)] at h
      peel h as x, hx
      peel h as s1, hs1
      peel h as i2, hi2
      rw [idx_cons hx, List.foldl_cons, ← usize_succ hi2]
      exact ih i2 s1 _ (by rw [usize_succ hi2]; omega) (hstep s y x s1 hs hs1) h
  exact key _ i s y rfl hs h

/-! ## One record -/

theorem emit_push_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {d : frontend.scan_types.DeclRec} (hd : DeclRecStrWF d) {v}
    (hv : alloc.vec.Vec.push st.out d = ok v) :
    EmitRel { st with out := v } (lst.push (absDeclRec d)) := by
  refine ⟨hs.visited, hs.inv, hs.names, hs.exprs, ?_, ?_⟩
  · show v.val.map absDeclRec = (lst.out.push (absDeclRec d)).toList
    rw [ConRon.Refine.vec_push_val hv, List.map_append, hs.out]; simp
  · intro x hx
    have hx' : x ∈ v.val := hx
    rw [ConRon.Refine.vec_push_val hv] at hx'
    rcases List.mem_append.mp hx' with h1 | h1
    · exact hs.wf x h1
    · rw [List.mem_singleton.mp h1]; exact hd

theorem hints_dup_eq {h r : frontend.scan_types.HintsRec}
    (e : frontend.olean.spec.hints_dup h = ok r) : r = h := by
  cases h <;> exact (Result.ok_injective (show ok _ = ok r from e)).symm

/-- The twin's `Emit.one` past the common part. -/
def oneK (st : Emit) (cv : CVRec) : ConLeche.Frontend.Olean.CKindF NIdx EIdx → Emit
  | .ax u => st.push (.ax cv u)
  | .defn v h s => let (st, i) := st.expr v; st.push (.defn cv i h s)
  | .thm v _ => let (st, i) := st.expr v; st.push (.thm cv i)
  | .opaq v u => let (st, i) := st.expr v; st.push (.opaq cv i u)
  | .quot k => st.push (.quot cv k)
  | _ => st

theorem one_eq_oneK (st : Emit) (c : Arena.Frontend.Olean.CEntry) :
    st.one c = oneK (st.cv c).1 (st.cv c).2 c.c.kind := by
  rw [Emit.one]
  cases c.c.kind <;> rfl

/-- **`emit_one` is `Emit.one`.** -/
theorem emit_one_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {c : frontend.olean.closure.CEntry} {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c')
    {st' : frontend.olean.emit.Emit} (h : emit_one st c = ok st') : EmitRel st' (lst.one c') := by
  rw [emit_one] at h
  peel h as q, hq
  obtain ⟨cv, st1⟩ := q
  obtain ⟨a1, b1⟩ := emit_cv_rel hs hc hq
  dsimp only at a1 b1
  rw [one_eq_oneK, ← a1]
  have hk := hc.1.kind
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try exact (hk : False).elim
  case Ax.ax u u' =>
    cases (hk : u = u')
    peel h as v, hv
    cases Result.ok_injective h
    exact emit_push_rel b1 (d := .Ax cv u) trivial hv
  case Defn.defn v hh s v' h' s' =>
    obtain ⟨rfl, rfl, rfl, hw⟩ := hk
    peel h as q2, h2
    obtain ⟨i, st2⟩ := q2
    obtain ⟨a2, b2⟩ := emit_expr_rel b1 h2
    peel h as hr, hhr
    peel h as v1, hv1
    peel h as v2, hv2
    cases Result.ok_injective h
    rw [hints_dup_eq hhr, ConRon.Refine.Expr.str_copy_eq hv1] at hv2
    dsimp only at a2 b2
    have := emit_push_rel a2 (d := .Defn cv i hh s) hw hv2
    rw [show absDeclRec (.Defn cv i hh s) = .defn (absCVRec cv) (absU64 i) (absHintsRec hh)
      (ConRon.Refine.absString s) from rfl, b2] at this
    exact this
  case Thm.thm v a v' a' =>
    obtain ⟨rfl, -⟩ := hk
    peel h as q2, h2
    obtain ⟨i, st2⟩ := q2
    obtain ⟨a2, b2⟩ := emit_expr_rel b1 h2
    peel h as v1, hv1
    cases Result.ok_injective h
    dsimp only at a2 b2
    have := emit_push_rel a2 (d := .Thm cv i) trivial hv1
    rw [show absDeclRec (.Thm cv i) = .thm (absCVRec cv) (absU64 i) from rfl, b2] at this
    exact this
  case Opaq.opaq v u v' u' =>
    obtain ⟨rfl, rfl⟩ := hk
    peel h as q2, h2
    obtain ⟨i, st2⟩ := q2
    obtain ⟨a2, b2⟩ := emit_expr_rel b1 h2
    peel h as v1, hv1
    cases Result.ok_injective h
    dsimp only at a2 b2
    have := emit_push_rel a2 (d := .Opaq cv i u) trivial hv1
    rw [show absDeclRec (.Opaq cv i u) = .opaq (absCVRec cv) (absU64 i) u from rfl, b2] at this
    exact this
  case Quot.quot s s' =>
    obtain ⟨rfl, hw⟩ := hk
    peel h as v1, hv1
    peel h as v2, hv2
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv1] at hv2
    exact emit_push_rel b1 (d := .Quot cv s) hw hv2
  all_goals (cases Result.ok_injective h; exact b1)

/-! ## A block's records -/

/-- An accumulator, one record further. -/
theorem acc_push {T T' : Type} {A : T → T'} {acc acc1 : alloc.vec.Vec T} {l : Array T'} {x : T}
    {a : T'} (ha : acc.val.map A = l.toList) (h : alloc.vec.Vec.push acc x = ok acc1)
    (e : A x = a) : acc1.val.map A = (l.push a).toList := by
  rw [ConRon.Refine.vec_push_val h, List.map_append, ha, ← e]; simp

theorem emit_ty_step_rel {st : frontend.olean.emit.Emit} {acc} {y : Emit × Array IndTypeRec}
    (hx : StAcc absIndTypeRec (st, acc) y) {c : frontend.olean.closure.CEntry}
    {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c') {o}
    (h : emit_ty_step st acc c = ok o) : StAcc absIndTypeRec o (Emit.tyStep y c') := by
  obtain ⟨lst, lacc⟩ := y
  obtain ⟨hs, ha⟩ := hx
  rw [emit_ty_step] at h
  have hk := hc.1.kind
  have e : Emit.tyStep (lst, lacc) c' = match c'.c.kind with
      | .induct np ni _ cs nn ir iu irf =>
        let (st, cv) := lst.cv c'
        let (st, cs) := st.names' cs
        (st, lacc.push { cv, ctors := cs, isRec := ir, isReflexive := irf, isUnsafe := iu,
                         numIndices := ni, numNested := nn, numParams := np : IndTypeRec })
      | _ => (lst, lacc) := rfl
  rw [e]
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try first
    | exact (hk : False).elim
    | (cases Result.ok_injective h; exact ⟨hs, ha⟩)
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨rfl, rfl, -, rfl, rfl, rfl, rfl, rfl⟩ := hk
    peel h as q1, h1
    obtain ⟨cv, st1⟩ := q1
    obtain ⟨a1, b1⟩ := emit_cv_rel hs hc h1
    peel h as q2, h2
    obtain ⟨ctors, st2⟩ := q2
    obtain ⟨a2, b2⟩ := emit_names_rel b1 h2
    peel h as acc1, hacc
    cases Result.ok_injective h
    refine ⟨b2, acc_push ha hacc ?_⟩
    show IndTypeRec.mk _ _ _ _ _ _ _ _ = IndTypeRec.mk _ _ _ _ _ _ _ _
    dsimp only at a1 a2
    rw [a1, a2]

theorem emit_ctor_step_rel {st : frontend.olean.emit.Emit} {acc} {y : Emit × Array IndCtorRec}
    (hx : StAcc absIndCtorRec (st, acc) y) {c : frontend.olean.closure.CEntry}
    {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c') {o}
    (h : emit_ctor_step st acc c = ok o) : StAcc absIndCtorRec o (Emit.ctorStep y c') := by
  obtain ⟨lst, lacc⟩ := y
  obtain ⟨hs, ha⟩ := hx
  rw [emit_ctor_step] at h
  have hk := hc.1.kind
  have e : Emit.ctorStep (lst, lacc) c' = match c'.c.kind with
      | .ctor ind cidx np nf iu =>
        let (st, cv) := lst.cv c'
        let (st, ii) := st.name ind
        (st, lacc.push { cv, isUnsafe := iu, numFields := nf, numParams := np,
                         cidx := some cidx, induct := some ii : IndCtorRec })
      | _ => (lst, lacc) := rfl
  rw [e]
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try first
    | exact (hk : False).elim
    | (cases Result.ok_injective h; exact ⟨hs, ha⟩)
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
    peel h as q1, h1
    obtain ⟨cv, st1⟩ := q1
    obtain ⟨a1, b1⟩ := emit_cv_rel hs hc h1
    peel h as q2, h2
    obtain ⟨ii, st2⟩ := q2
    obtain ⟨b2, a2⟩ := emit_name_rel b1 h2
    peel h as acc1, hacc
    cases Result.ok_injective h
    refine ⟨b2, acc_push ha hacc ?_⟩
    show IndCtorRec.mk _ _ _ _ _ _ = IndCtorRec.mk _ _ _ _ _ _
    dsimp only at a1 a2
    rw [a1, ← a2]
    rfl

theorem emit_rule_step_rel {st : frontend.olean.emit.Emit} {acc} {y : Emit × Array RuleRec}
    (hx : StAcc absRuleRec (st, acc) y) {r : arena.handle.NIdx × Std.U64 × arena.handle.EIdx}
    {r' : NIdx × Nat × EIdx} (hr : RuleR r r') {o}
    (h : emit_rule_step st acc r = ok o) : StAcc absRuleRec o (Emit.ruleStep y r') := by
  obtain ⟨lst, lacc⟩ := y
  obtain ⟨hs, ha⟩ := hx
  obtain ⟨n, i, e⟩ := r
  obtain ⟨n', i', e'⟩ := r'
  obtain ⟨rfl, rfl, rfl⟩ := hr
  rw [emit_rule_step] at h
  peel h as q1, h1
  obtain ⟨ci, st1⟩ := q1
  obtain ⟨b1, a1⟩ := emit_name_rel hs h1
  peel h as q2, h2
  obtain ⟨ri, st2⟩ := q2
  obtain ⟨b2, a2⟩ := emit_expr_rel b1 h2
  peel h as acc1, hacc
  cases Result.ok_injective h
  refine ⟨b2, acc_push ha hacc ?_⟩
  dsimp only at a1 a2
  show RuleRec.mk _ _ _ = RuleRec.mk _ _ _
  rw [a1, a2]
  rfl


theorem emit_rec_step_loop_rel (rules : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (k : Nat) : ∀ (st : frontend.olean.emit.Emit) (rr : alloc.vec.Vec frontend.scan_types.RuleRec)
      (y : Emit × Array RuleRec) (i : Std.Usize) (l' : List (NIdx × Nat × EIdx)) (o),
      StAcc absRuleRec (st, rr) y → List.Forall₂ RuleR (rules.val.drop i.val) l' →
      rules.val.length - i.val = k → emit_rec_step_loop st rules rr i = ok o →
      StAcc absRuleRec o (l'.foldl Emit.ruleStep y) := by
  induction k with
  | zero =>
    intro st rr y i l' o hx hl hk h
    rw [emit_rec_step_loop, ite_eq_right (not_lt_len hk)] at h
    cases Result.ok_injective h
    rw [drop_stop hk] at hl
    cases hl
    exact hx
  | succ k ih =>
    intro st rr y i l' o hx hl hk h
    rw [emit_rec_step_loop, ite_eq_left (lt_len hk)] at h
    peel h as t, ht
    peel h as q, hq
    obtain ⟨st1, rr1⟩ := q
    peel h as i2, hi2
    rw [idx_cons ht] at hl
    cases hl with
    | cons hr hl =>
      rw [List.foldl_cons]
      refine ih st1 rr1 _ i2 _ o (emit_rule_step_rel hx hr hq) ?_ (by rw [usize_succ hi2]; omega) h
      rw [usize_succ hi2]
      exact hl

theorem emit_rec_step_rel {st : frontend.olean.emit.Emit} {acc} {y : Emit × Array IndRecRec}
    (hx : StAcc absIndRecRec (st, acc) y) {c : frontend.olean.closure.CEntry}
    {c' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel c c') {o}
    (h : emit_rec_step st acc c = ok o) : StAcc absIndRecRec o (Emit.recStep y c') := by
  obtain ⟨lst, lacc⟩ := y
  obtain ⟨hs, ha⟩ := hx
  rw [emit_rec_step] at h
  have hk := hc.1.kind
  have e : Emit.recStep (lst, lacc) c' = match c'.c.kind with
      | .recur _ np ni nmo nmi rules k iu =>
        let (st, cv) := lst.cv c'
        let (st, rr) := rules.foldl Emit.ruleStep (st, #[])
        (st, lacc.push { cv, isUnsafe := iu, k, numIndices := ni, numMinors := nmi,
                         numMotives := nmo, numParams := np, rules := rr.toList : IndRecRec })
      | _ => (lst, lacc) := rfl
  rw [e]
  generalize c.c.kind = k at h hk
  generalize c'.c.kind = k' at hk ⊢
  cases k <;> cases k' <;> try first
    | exact (hk : False).elim
    | (cases Result.ok_injective h; exact ⟨hs, ha⟩)
  case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨-, rfl, rfl, rfl, rfl, hr, rfl, rfl⟩ := hk
    peel h as q1, h1
    obtain ⟨cv, st1⟩ := q1
    obtain ⟨a1, b1⟩ := emit_cv_rel hs hc h1
    peel h as q2, h2
    obtain ⟨st2, rr1⟩ := q2
    obtain ⟨b2, a2⟩ := emit_rec_step_loop_rel rules _ st1 _ (((lst.cv c').1, #[])) 0#usize rules' _
      ⟨b1, rfl⟩ hr rfl h2
    peel h as acc1, hacc
    cases Result.ok_injective h
    refine ⟨b2, acc_push ha hacc ?_⟩
    dsimp only at a1 a2
    show IndRecRec.mk _ _ _ _ _ _ _ _ = IndRecRec.mk _ _ _ _ _ _ _ _
    rw [a1]
    exact congrArg _ a2

/-! ## By name: the merge's constants -/

/-- A step at a name of the merge, on the twin's side. -/
def namedF {β : Type} (f : β → Arena.Frontend.Olean.CEntry → β) (mg' : Arena.Frontend.Olean.Merged)
    (y : β) (a : NIdx) : β :=
  match mg'.get a with
  | some c => f y c
  | none => y

/-- `(entriesOf mg ns).foldl f`, a name at a time. -/
theorem entries_foldl {β : Type} (f : β → Arena.Frontend.Olean.CEntry → β)
    (mg' : Arena.Frontend.Olean.Merged) (ns : List NIdx) (y : β) :
    (entriesOf mg' ns).foldl f y = ns.foldl (namedF f mg') y := by
  induction ns generalizing y with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ← ih, namedF]
    simp only [entriesOf, List.filterMap_cons]
    cases mg'.get a <;> rfl

/-- **A step at a name**: the Rust's `mg_get` and the twin's `Merged.get` agree. -/
theorem named_rel {S S' : Type} {Rel : S → S' → Prop}
    {step : S → frontend.olean.closure.CEntry → Result S}
    {f : S' → Arena.Frontend.Olean.CEntry → S'}
    (hstep : ∀ s y c c' o, Rel s y → CEntryRel c c' → step s c = ok o → Rel o (f y c'))
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {n : arena.handle.NIdx} {s : S} {y : S'} {o : S} (hs : Rel s y)
    (h : (do
      let o1 ← frontend.olean.merge.mg_get mg n
      match o1 with
      | none => ok s
      | some c => step s c) = ok o) : Rel o (namedF f mg' y (absNIdx n)) := by
  peel h as o1, h1
  have hr := mg_get_rel hm h1
  rw [namedF]
  cases hg : mg'.get (absNIdx n) with
  | none =>
    rw [hg] at hr
    cases hr
    cases Result.ok_injective h
    exact hs
  | some c' =>
    rw [hg] at hr
    cases hr with
    | some hc => exact hstep _ _ _ _ _ hs hc h

/-- A fold over a mapped list. -/
theorem foldl_map' {α β γ : Type} (g : α → β) (f : γ → β → γ) (l : List α) (y : γ) :
    (l.map g).foldl f y = l.foldl (fun y x => f y (g x)) y := List.foldl_map ..

/-- **`emit_ones` is `Emit.ones`.** -/
theorem emit_ones_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {cs : alloc.vec.Vec arena.handle.NIdx} {st' : frontend.olean.emit.Emit}
    (h : emit_ones st mg cs = ok st') : EmitRel st' (lst.ones mg' (cs.val.map absNIdx)) := by
  rw [emit_ones] at h
  have := up_loop (L := fun s i => emit_ones_loop s mg cs i) cs
    (step := fun s x => one_named s mg x) (Rel := EmitRel)
    (f := fun y x => namedF Emit.one mg' y (absNIdx x))
    (fun s i => by rw [emit_ones_loop])
    (fun s y x s1 hs h1 => by
      rw [one_named] at h1
      exact named_rel (Rel := EmitRel) (fun _ _ _ _ _ a b c => emit_one_rel a b c) hm hs h1) hs h
  rw [Emit.ones, entries_foldl, foldl_map']
  exact this

theorem one_named_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {n : arena.handle.NIdx} {st' : frontend.olean.emit.Emit} (h : one_named st mg n = ok st') :
    EmitRel st' (lst.ones mg' [absNIdx n]) := by
  rw [one_named] at h
  rw [Emit.ones, entries_foldl]
  exact named_rel (Rel := EmitRel) (fun _ _ _ _ _ a b c => emit_one_rel a b c) hm hs h

/-- **`emit_block` is `Emit.block`.** -/
theorem emit_block_rel {st : frontend.olean.emit.Emit} {lst : Emit} (hs : EmitRel st lst)
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    {tys ctors recs : alloc.vec.Vec arena.handle.NIdx} {st' : frontend.olean.emit.Emit}
    (h : emit_block st mg tys ctors recs = ok st') :
    EmitRel st' (lst.block mg' (tys.val.map absNIdx) (ctors.val.map absNIdx) (recs.val.map absNIdx)) := by
  rw [emit_block] at h
  peel h as q1, h1
  obtain ⟨st1, ts⟩ := q1
  peel h as q2, h2
  obtain ⟨st2, cts⟩ := q2
  peel h as q3, h3
  obtain ⟨st3, rs⟩ := q3
  peel h as v, hv
  cases Result.ok_injective h
  have r1 := up_loop (L := fun s i => emit_block_loop0 s.1 mg tys s.2 i) tys
    (s := (st, _)) (y := (lst, #[]))
    (step := fun s x => ty_named s.1 mg s.2 x) (Rel := StAcc absIndTypeRec)
    (f := fun y x => namedF Emit.tyStep mg' y (absNIdx x))
    (fun s i => by rw [emit_block_loop0]; rfl)
    (fun s y x s1 hs h1 => by
      rw [ty_named] at h1
      exact named_rel (Rel := StAcc absIndTypeRec) (step := fun s c => emit_ty_step s.1 s.2 c)
        (fun _ _ _ _ _ a b c => emit_ty_step_rel a b c) hm hs h1) ⟨hs, rfl⟩ h1
  have r2 := up_loop (L := fun s i => emit_block_loop1 s.1 mg ctors s.2 i) ctors
    (s := (st1, _)) (y := (_, #[]))
    (step := fun s x => ctor_named s.1 mg s.2 x) (Rel := StAcc absIndCtorRec)
    (f := fun y x => namedF Emit.ctorStep mg' y (absNIdx x))
    (fun s i => by rw [emit_block_loop1]; rfl)
    (fun s y x s1 hs h1 => by
      rw [ctor_named] at h1
      exact named_rel (Rel := StAcc absIndCtorRec) (step := fun s c => emit_ctor_step s.1 s.2 c)
        (fun _ _ _ _ _ a b c => emit_ctor_step_rel a b c) hm hs h1) ⟨r1.1, rfl⟩ h2
  have r3 := up_loop (L := fun s i => emit_block_loop2 s.1 mg recs s.2 i) recs
    (s := (st2, _)) (y := (_, #[]))
    (step := fun s x => rec_named s.1 mg s.2 x) (Rel := StAcc absIndRecRec)
    (f := fun y x => namedF Emit.recStep mg' y (absNIdx x))
    (fun s i => by rw [emit_block_loop2]; rfl)
    (fun s y x s1 hs h1 => by
      rw [rec_named] at h1
      exact named_rel (Rel := StAcc absIndRecRec) (step := fun s c => emit_rec_step s.1 s.2 c)
        (fun _ _ _ _ _ a b c => emit_rec_step_rel a b c) hm hs h1) ⟨r2.1, rfl⟩ h3
  have e := emit_push_rel r3.1 (d := .Ind ts cts rs) trivial hv
  rw [Emit.block]
  simp only [entries_foldl, foldl_map']
  rw [show absDeclRec (.Ind ts cts rs) = .ind (absIndTypeRecs ts) (absIndCtorRecs cts)
    (absIndRecRecs rs) from rfl, absIndTypeRecs, absIndCtorRecs, absIndRecRecs,
    show List.map absIndTypeRec ts.val = _ from r1.2, show List.map absIndCtorRec cts.val = _ from r2.2,
    show List.map absIndRecRec rs.val = _ from r3.2] at e
  exact e

/-! ## The stored names -/

theorem foldl_filter_app {α β : Type} (g : α → β) (p : β → Bool) (xs : List α) (l : List β) :
    xs.foldl (fun l x => if p (g x) = true then l ++ [g x] else l) l = l ++ (xs.map g).filter p := by
  induction xs generalizing l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.filter_cons]
    by_cases h : p (g a) = true <;> simp [h]

/-- `push_stored` and `block_tys`' loop: the stored names pushed on. -/
theorem stored_step {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {out : alloc.vec.Vec arena.handle.NIdx} {l : List NIdx}
    (hl : out.val.map absNIdx = l) {x : arena.handle.NIdx} {out1}
    (h : (do
      let b ← frontend.olean.merge.mg_has mg x
      if b = true then do
        let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x
        alloc.vec.Vec.push out n1
      else ok out) = ok out1) :
    out1.val.map absNIdx =
      if mg'.map.contains (absNIdx x) = true then l ++ [absNIdx x] else l := by
  peel h as b, hb
  rw [← mg_has_eq hm hb]
  cases b with
  | false =>
    cases Result.ok_injective h
    simpa using hl
  | true =>
    rw [ite_eq_left rfl] at h
    peel h as n1, hn1
    rw [nidx_dup2_ok hn1] at h
    rw [ConRon.Refine.vec_push_val h, List.map_append, hl]
    simp

theorem push_stored_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {cs out : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_stored mg cs out = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++ blockTys mg' (cs.val.map absNIdx) := by
  rw [push_stored] at h
  have := up_loop (L := fun s i => push_stored_loop mg cs s i) cs
    (step := fun s x => do
      let b ← frontend.olean.merge.mg_has mg x
      if b = true then do
        let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x
        alloc.vec.Vec.push s n1
      else ok s)
    (Rel := fun s l => s.val.map absNIdx = l)
    (f := fun l x => if (fun n => mg'.map.contains n) (absNIdx x) = true then l ++ [absNIdx x] else l)
    (fun s i => by
      rw [push_stored_loop]
      refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
      exact congrArg (Std.bind _) (funext fun x => (Std.bind_assoc ..).symm))
    (fun s y x s1 hs h1 => stored_step hm hs h1) rfl h
  rw [foldl_filter_app] at this
  exact this

theorem block_tys_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {all o : alloc.vec.Vec arena.handle.NIdx} (h : block_tys mg all = ok o) :
    o.val.map absNIdx = blockTys mg' (all.val.map absNIdx) := by
  rw [block_tys] at h
  have := up_loop (L := fun s i => block_tys_loop mg all s i) all
    (step := fun s x => do
      let b ← frontend.olean.merge.mg_has mg x
      if b = true then do
        let n1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x
        alloc.vec.Vec.push s n1
      else ok s)
    (Rel := fun s l => s.val.map absNIdx = l) (y := [])
    (f := fun l x => if (fun n => mg'.map.contains n) (absNIdx x) = true then l ++ [absNIdx x] else l)
    (fun s i => by
      rw [block_tys_loop]
      refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
      exact congrArg (Std.bind _) (funext fun x => (Std.bind_assoc ..).symm))
    (fun s y x s1 hs h1 => stored_step hm hs h1) rfl h
  rw [foldl_filter_app] at this
  simpa [blockTys] using this

/-- The step of the twin's `blockCtors`. -/
def ctorsOf (mg' : Arena.Frontend.Olean.Merged) (t : NIdx) : List NIdx :=
  match mg'.get t with
  | some c => match c.c.kind with
    | .induct _ _ _ cs _ _ _ _ => blockTys mg' cs
    | _ => []
  | none => []

theorem block_ctors_of_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {out o : alloc.vec.Vec arena.handle.NIdx}
    (h : block_ctors_of mg n out = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++ ctorsOf mg' (absNIdx n) := by
  rw [block_ctors_of] at h
  peel h as o1, h1
  have hr := mg_get_rel hm h1
  rw [ctorsOf]
  cases hg : mg'.get (absNIdx n) with
  | none =>
    rw [hg] at hr
    cases hr
    cases Result.ok_injective h
    simp
  | some c' =>
    rw [hg] at hr
    cases hr with
    | some hc =>
      have hk := hc.1.kind
      dsimp only at h ⊢
      generalize KindRelK : frontend.olean.spec.CEntryF.kind _ = k at h hk
      generalize c'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try first
        | exact (hk : False).elim
        | (cases Result.ok_injective h; simp)
      case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
        obtain ⟨-, -, -, rfl, -⟩ := hk
        exact push_stored_rel hm h

theorem foldl_flat_app {α β : Type} (g : α → List β) (xs : List α) (l : List β) :
    xs.foldl (fun l x => l ++ g x) l = l ++ xs.flatMap g := by
  induction xs generalizing l with
  | nil => simp
  | cons a t ih => rw [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

theorem block_ctors_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {tys o : alloc.vec.Vec arena.handle.NIdx}
    (h : block_ctors mg tys = ok o) :
    o.val.map absNIdx = blockCtors mg' (tys.val.map absNIdx) := by
  rw [block_ctors] at h
  have := up_loop (L := fun s i => block_ctors_loop mg tys s i) tys
    (step := fun s x => block_ctors_of mg x s)
    (Rel := fun s l => s.val.map absNIdx = l) (y := [])
    (f := fun l x => l ++ ctorsOf mg' (absNIdx x))
    (fun s i => by rw [block_ctors_loop])
    (fun s y x s1 hs h1 => by rw [block_ctors_of_rel hm h1, hs]) rfl h
  rw [foldl_flat_app] at this
  have e : blockCtors mg' (tys.val.map absNIdx) = (tys.val.map absNIdx).flatMap (ctorsOf mg') := rfl
  rw [e, List.flatMap_map]
  simpa using this

theorem quot_names_rel {pk : frontend.olean.spec.OleanPins} {o : alloc.vec.Vec arena.handle.NIdx}
    (h : quot_names pk = ok o) : o.val.map absNIdx = quotNames (absPins pk) := by
  rw [quot_names] at h
  peel h as n, hn
  peel h as v1, hv1
  peel h as n1, hn1
  peel h as v2, hv2
  peel h as n2, hn2
  peel h as v3, hv3
  peel h as n3, hn3
  rw [ConRon.Refine.vec_push_val h, ConRon.Refine.vec_push_val hv3, ConRon.Refine.vec_push_val hv2,
    ConRon.Refine.vec_push_val hv1, nidx_dup2_ok hn, nidx_dup2_ok hn1, nidx_dup2_ok hn2, nidx_dup2_ok hn3]
  rfl

theorem quot_constants_rel {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {o : alloc.vec.Vec arena.handle.NIdx}
    (h : quot_constants pk mg = ok o) : o.val.map absNIdx = quotConstants (absPins pk) mg' := by
  rw [quot_constants] at h
  peel h as v, hv
  rw [block_tys_rel hm h, quot_names_rel hv]
  rfl

/-- **The recursors' map against the twin's.** -/
structure RecMapRel (m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec arena.handle.NIdx))
    (m' : Std.HashMap NIdx (Array NIdx)) : Prop where
  map : ConRon.Refine.HashMap2.RelOn anyN m m' absNIdx (fun v => (v.val.map absNIdx).toArray)
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m

theorem block_recs_rel {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {m m'} (hr : RecMapRel m m') {n : arena.handle.NIdx}
    {o : alloc.vec.Vec arena.handle.NIdx} (h : block_recs mg m n = ok o) :
    o.val.map absNIdx = blockRecs mg' m' (absNIdx n) := by
  rw [block_recs] at h
  peel h as o1, h1
  have hk := hr.map n trivial
  rw [← nidx_get hr.inv h1] at hk
  rw [blockRecs, ← hk]
  cases o1 with
  | none =>
    cases Result.ok_injective h
    rfl
  | some a =>
    rw [block_tys_rel hm h]
    simp

end ConRon.Refine2.Frontend.Olean



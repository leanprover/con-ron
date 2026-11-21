/-
# `ConRon.Refine2.Modular.Graph` — `modular/graph.rs`: the import graph of a closure, checked

**Task #166, Theorem 2.**  Every function of `graph.rs` against its twin
(`Arena/Modular/Graph.lean`).  The pure ones are equations under the abstraction (a `Vec` is its
list, a `u64` its value, a `HashMap2` keyed by handles the twin's `Std.HashSet`/`Std.HashMap`
of what the handles stand for); the ones that reach a header read (`hdr_of`, `level_hdrs`,
`closure_levels`, `graph_of`) claim their accept (`AS`).  `missing_on`, `file_at`,
`fault_error` and `cycle_msg` only build failures, which claim nothing.

**Casts.**  The Rust stores positions as `u64` and reads them back as `usize`
(`as usize`, which truncates).  Each equation that reads a position back takes the
premise that every position it reads fits a `usize` (`FitsN`, `IdxRel.fit`); the positions
the walk makes are `usize` lengths and counters, so the premise holds where `graph_of`
uses them.
-/
import ConRon.Refine2.Frontend.Olean.ClosureRead
import ConRon.Arena.Modular.Graph

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.graph

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Arena.Modular (Node)
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine.HashMap2 (Inv toFun)

/-! ## The abstraction -/

/-- An import, as the twin's. -/
@[reducible] def absImp (i : frontend.olean.spec.ImportF arena.handle.NIdx) :
    ConLeche.Frontend.Olean.ImportF NIdx :=
  absImportF absNIdx i

/-- A node of the closure, as the twin's. -/
@[reducible] def absNode (p : arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    Node :=
  (absNIdx p.1, absImports p.2)

/-- The closure, as the twin's. -/
@[reducible] def absC (c : alloc.vec.Vec (arena.handle.NIdx ×
    alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))) : _root_.Array Node :=
  (c.val.map absNode).toArray

/-- The pair of a compared run, as the twin's. -/
@[reducible] def absCmp (cmp : Option (arena.handle.NIdx × arena.handle.NIdx)) : Option (NIdx × NIdx) :=
  cmp.map fun p => (absNIdx p.1, absNIdx p.2)

/-- Numbers, as the twin's. -/
@[reducible] def absNat (v : alloc.vec.Vec Std.U64) : _root_.Array Nat := (v.val.map (·.val)).toArray

/-- Each position's numbers, as the twin's. -/
@[reducible] def absDeps (v : alloc.vec.Vec (alloc.vec.Vec Std.U64)) : _root_.Array (_root_.Array Nat) :=
  (v.val.map absNat).toArray

/-- An optional number, as the twin's. -/
@[reducible] def absOpt (o : Option Std.U64) : Option Nat := o.map (·.val)

/-- The ranks, as the twin's. -/
@[reducible] def absRanks (v : alloc.vec.Vec (Option Std.U64)) : _root_.Array (Option Nat) :=
  (v.val.map absOpt).toArray

/-- A fault, as the twin's. -/
def absFault : frontend.modular.graph.Fault → Modular.Fault
  | .Root r => .root (absNIdx r)
  | .Unranked m => .unranked (absNIdx m)
  | .Twice => .twice
  | .Edge m i => .edge (absNIdx m) (i.map absNIdx)

/-- Every number read back as a position fits a `usize`. -/
def FitsN (v : alloc.vec.Vec Std.U64) : Prop := ∀ x ∈ v.val, x.val ≤ Std.Usize.max

/-- … at every position. -/
def FitsD (v : alloc.vec.Vec (alloc.vec.Vec Std.U64)) : Prop := ∀ d ∈ v.val, FitsN d

/-! ## Small facts -/

theorem nidx_eq2_val {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

theorem import_rec_dup_ok {i o : frontend.olean.spec.ImportF arena.handle.NIdx}
    (h : frontend.olean.levels.import_rec_dup i = ok o) : o = i := by
  rw [frontend.olean.levels.import_rec_dup] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  cases Result.ok_injective h
  rfl

theorem usize_succ {i i2 : Std.Usize} (h : i + 1#usize = ok i2) : i2.val = i.val + 1 := by
  rw [ConRon.Refine.Nat.uadd_val h]; rfl

theorem not_lt_len {α : Type} {i : Std.Usize} {v : alloc.vec.Vec α} (h : ¬ i < alloc.vec.Vec.len v) :
    v.val.length ≤ i.val := by
  have : ¬ i.val < (alloc.vec.Vec.len v).val := h
  rw [vec_len_val] at this; omega

theorem lt_len {α : Type} {i : Std.Usize} {v : alloc.vec.Vec α} (h : i < alloc.vec.Vec.len v) :
    i.val < v.val.length := by
  have : i.val < (alloc.vec.Vec.len v).val := h
  rwa [vec_len_val] at this

theorem cast_u64_val {i : Std.Usize} {x : Std.U64} (h : lift (UScalar.cast .U64 i) = (ok x : Result Std.U64)) :
    x.val = i.val := by
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [usize_cast_u64_val']

theorem cast_usize_val {i : Std.U64} {x : Std.Usize} (hi : i.val ≤ Std.Usize.max)
    (h : lift (UScalar.cast .Usize i) = (ok x : Result Std.Usize)) : x.val = i.val := by
  rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hi]
  exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective h).symm

theorem vec_new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

theorem vec_with_capacity_val {α : Type} (n : Std.Usize) : (alloc.vec.Vec.with_capacity α n).val = [] := rfl

theorem vec_len_le {α : Type} (v : alloc.vec.Vec α) : v.val.length ≤ Std.Usize.max := v.property

/-! ## `solution_import`, `cmp_extra` -/

/-- **`solution_import` is `solutionImport`.** -/
theorem solution_import_eq {s : arena.handle.NIdx} {o} (h : solution_import s = ok o) :
    absImp o = Modular.solutionImport (absNIdx s) := by
  rw [solution_import] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  cases Result.ok_injective h
  rfl

/-- **`cmp_extra` is `cmpExtra`.** -/
theorem cmp_extra_eq {cmp : Option (arena.handle.NIdx × arena.handle.NIdx)} {m : arena.handle.NIdx} {o}
    (h : cmp_extra cmp m = ok o) : absImports o = Modular.cmpExtra (absCmp cmp) (absNIdx m) := by
  cases cmp with
  | none =>
    rw [cmp_extra] at h
    cases Result.ok_injective h
    rfl
  | some p =>
    obtain ⟨c, s⟩ := p
    rw [cmp_extra] at h
    peel h as b, hb
    have eb := nidx_eq2_val hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as x, hx
      have ex := solution_import_eq hx
      have ho := ConRon.Refine.vec_push_val h
      rw [vec_new_val] at ho
      simp only [Modular.cmpExtra, absCmp, Option.map_some]
      rw [ite_eq_left (by rw [← eb]; exact cb)]
      simp [absImports, ho, ← ex]
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      simp only [Modular.cmpExtra, absCmp, Option.map_some]
      rw [ite_eq_right (by rw [← eb]; exact cb)]
      rfl

/-! ## The tables -/

/-- The handles' hash. -/
abbrev hN := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
/-- The handles' equality. -/
abbrev eN := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2

/-- **A table of positions by handle**, as the twin's map of what the handles stand for; every
position fits a `usize`. -/
structure IdxRel (m : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) (s : _root_.Std.HashMap NIdx Nat) :
    Prop where
  inv : Inv hN m
  get : ∀ k, (toFun m k).map (·.val) = s[absNIdx k]?
  fit : ∀ k v, toFun m k = some v → v.val ≤ Std.Usize.max

theorem IdxRel.get_eq {m s} (h : IdxRel m s) {k : arena.handle.NIdx} {o : Option Std.U64}
    (hg : ron.hashmap2.HashMap2.get hN eN m k = ok o) :
    absOpt o = s[absNIdx k]? ∧ ∀ v, o = some v → v.val ≤ Std.Usize.max := by
  rw [ConRon.Refine.HashMap2.get_refines_gen (P := fun _ => True) nidx_eq2 h.inv (fun _ _ => trivial)
    trivial hg]
  exact ⟨h.get k, h.fit k⟩

theorem IdxRel.insert {m s} (h : IdxRel m s) {k : arena.handle.NIdx} {v : Std.U64} {old} {m'}
    (hv : v.val ≤ Std.Usize.max)
    (hi : ron.hashmap2.HashMap2.insert hN eN m k v = ok (old, m')) :
    IdxRel m' (s.insert (absNIdx k) v.val) := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen (P := fun _ => True) nidx_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_, fun k1 v1 hk1 => ?_⟩
  · rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
    by_cases hk : k1 = k
    · subst hk; simp
    · have hne : (absNIdx k == absNIdx k1) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun he => hk (absNIdx_inj he).symm
      rw [ite_eq_right hk, hne]
      simpa using h.get k1
  · rw [hupd, Function.update_apply] at hk1
    by_cases hk : k1 = k
    · rw [ite_eq_left hk] at hk1; cases hk1; exact hv
    · rw [ite_eq_right hk] at hk1; exact h.fit k1 v1 hk1

theorem IdxRel.empty {m : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64}
    (hn : ron.hashmap2.HashMap2.new arena.handle.NIdx Std.U64 = ok m) : IdxRel m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hN) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp, fun k v hk => by rw [hnone] at hk; cases hk⟩

/-! ## `idx_lookup`, `rank_of`, `rank_lt`, `edge_ok` -/

/-- **`idx_lookup` is `idx[m]?`.** -/
theorem idx_lookup_eq {idx s} (hidx : IdxRel idx s) {m : arena.handle.NIdx} {o}
    (h : idx_lookup idx m = ok o) : absOpt o = s[absNIdx m]? := by
  rw [idx_lookup] at h
  peel h as o1, ho1
  have e := (hidx.get_eq ho1).1
  cases o1 with
  | none => cases Result.ok_injective h; exact e
  | some _ => cases Result.ok_injective h; exact e

/-- **`rank_of` is `rankOf`.** -/
theorem rank_of_eq {idx s} (hidx : IdxRel idx s) {rank : alloc.vec.Vec (Option Std.U64)}
    {m : arena.handle.NIdx} {o} (h : rank_of idx rank m = ok o) :
    absOpt o = Modular.rankOf s (absRanks rank) (absNIdx m) := by
  rw [rank_of] at h
  peel h as o1, ho1
  obtain ⟨e, hfit⟩ := hidx.get_eq ho1
  simp only [Modular.rankOf, ← e]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some k =>
    dsimp only at h
    peel h as i, hi
    have hiv := cast_usize_val (hfit k rfl) hi
    simp only [absOpt, Option.map_some, Option.bind_some]
    by_cases hlt : i < alloc.vec.Vec.len rank
    · rw [ite_eq_left hlt] at h
      peel h as o2, ho2
      obtain ⟨hb, rfl⟩ := vec_index_eq ho2
      have hb' : k.val < rank.val.length := by rw [← hiv]; exact hb
      have eg : (absRanks rank)[k.val]? = some (absOpt rank.val[k.val]) := by
        simp [absRanks, hb']
      rw [eg, Option.join_some]
      simp only [hiv] at h
      cases hr : rank.val[k.val] with
      | none => rw [hr] at h; cases Result.ok_injective h; rfl
      | some r => rw [hr] at h; cases Result.ok_injective h; rfl
    · rw [ite_eq_right hlt] at h
      cases Result.ok_injective h
      have hle := not_lt_len hlt
      rw [hiv] at hle
      have eg : (absRanks rank)[k.val]? = none := by simp [absRanks]; omega
      rw [eg]; rfl

/-- **`rank_lt` is `rankLt`.** -/
theorem rank_lt_eq {a b : Option Std.U64} {o} (h : rank_lt a b = ok o) :
    o = ConLeche.Driver.Graph.rankLt (absOpt a) (absOpt b) := by
  rw [rank_lt.eq_def] at h
  cases a with
  | none => cases Result.ok_injective h; rfl
  | some x =>
    cases b with
    | none => cases Result.ok_injective h; rfl
    | some y =>
      cases Result.ok_injective h
      simp only [absOpt, Option.map_some, ConLeche.Driver.Graph.rankLt]
      rfl

/-- **`edge_ok` is `edgeOk`.** -/
theorem edge_ok_eq {pos p idx s} (hpos : NSet pos p) (hidx : IdxRel idx s)
    {rank : alloc.vec.Vec (Option Std.U64)} {m : arena.handle.NIdx}
    {i : frontend.olean.spec.ImportF arena.handle.NIdx} {o}
    (h : edge_ok pos idx rank m i = ok o) :
    o = Modular.edgeOk p (Modular.rankOf s (absRanks rank)) (absNIdx m) (absImp i) := by
  rw [edge_ok] at h
  peel h as b, hb
  have eb := SetRel.contains_key nidx_eq2 hpos hb
  simp only [Modular.edgeOk, absImp, absImportF]
  by_cases cb : b = true
  · rw [ite_eq_left cb] at h
    peel h as o1, ho1
    peel h as o2, ho2
    rw [rank_lt_eq h, rank_of_eq hidx ho1, rank_of_eq hidx ho2, ← eb, cb, Bool.true_and]
  · rw [ite_eq_right cb] at h
    cases Result.ok_injective h
    rw [← eb]; simp at cb; rw [cb, Bool.false_and]

/-! ## `names_of`, `dedup`, `index_of`, `deps_of` -/

theorem drop_cons_of_lt {α : Type} {l : List α} {i : Nat} (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi

theorem names_of_loop_eq (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    {s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {S : _root_.Std.HashSet NIdx} (hs : NSet s S)
    (k : Std.Usize) {o} (h : names_of_loop c s k = ok o) :
    NSet o (((c.val.drop k.val).map absNode).foldl (fun s e => s.insert e.1) S) := by
  rw [names_of_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, v⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as ⟨_, s1⟩, hs1
    peel h as k1, hk1
    have ih := names_of_loop_eq c (SetRel.insert nidx_eq2 absNIdx_inj hs hs1) k1 h
    rw [usize_succ hk1] at ih
    rw [drop_cons_of_lt hi, ← he]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact hs
termination_by c.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- **`names_of` is `namesOf`.** -/
theorem names_of_eq {c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))} {o}
    (h : names_of c = ok o) : NSet o (Modular.namesOf (absC c).toList) := by
  rw [names_of] at h
  peel h as s, hs
  have := names_of_loop_eq c (nset_empty hs) _ h
  simpa [Modular.namesOf] using this

theorem dedup_loop_eq (xs : alloc.vec.Vec arena.handle.NIdx)
    {s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {S : _root_.Std.HashSet NIdx} (hs : NSet s S)
    {acc : alloc.vec.Vec arena.handle.NIdx} (i : Std.Usize) {o}
    (h : dedup_loop xs s acc i = ok o) :
    let r := ((xs.val.drop i.val).map absNIdx).foldl (fun (sa : _root_.Std.HashSet NIdx × _root_.Array NIdx) x =>
      if sa.1.contains x then (sa.1, sa.2) else (sa.1.insert x, sa.2.push x)) (S, (acc.val.map absNIdx).toArray)
    o.1.val.map absNIdx = r.2.toList ∧ NSet o.2 r.1 := by
  rw [dedup_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len xs
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [drop_cons_of_lt hi, List.map_cons, List.foldl_cons]
    peel h as ⟨s1, acc1⟩, hq
    peel h as i2, hi2
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hq
      cases Result.ok_injective hq
      have ih := dedup_loop_eq xs hs i2 h
      rw [usize_succ hi2] at ih
      rw [ite_eq_left (by rw [← eb]; exact cb)]
      exact ih
    · rw [ite_eq_right cb] at hq
      peel hq as n1, hn1
      cases nidx_dup2_ok hn1
      peel hq as ⟨_, s2⟩, hs2
      peel hq as n2, hn2
      cases nidx_dup2_ok hn2
      peel hq as acc2, hacc2
      have ea : (acc2.val.map absNIdx).toArray = (acc.val.map absNIdx).toArray.push (absNIdx xs.val[i.val]) := by
        rw [ConRon.Refine.vec_push_val hacc2]; simp
      have hs2' := SetRel.insert nidx_eq2 absNIdx_inj hs hs2
      cases Result.ok_injective hq
      have ih := dedup_loop_eq xs hs2' i2 h
      rw [usize_succ hi2] at ih
      rw [ite_eq_right (by rw [← eb]; simpa using cb)]
      rw [← ea]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨by simp, hs⟩
termination_by xs.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hi2]; omega)

/-- **`dedup` is `dedup`.** -/
theorem dedup_eq {xs : alloc.vec.Vec arena.handle.NIdx} {o} (h : dedup xs = ok o) :
    o.1.val.map absNIdx = (Modular.dedup (xs.val.map absNIdx)).1 ∧
      NSet o.2 (Modular.dedup (xs.val.map absNIdx)).2 := by
  rw [dedup] at h
  peel h as s, hs
  have := dedup_loop_eq xs (nset_empty hs) (acc := alloc.vec.Vec.new _) _ h
  simpa [Modular.dedup, vec_new_val] using this

theorem index_of_loop_eq (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    {idx : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {S : _root_.Std.HashMap NIdx Nat}
    (hs : IdxRel idx S) (k : Std.Usize) {o} (h : index_of_loop c idx k = ok o) :
    IdxRel o (((c.val.drop k.val).map absNode).foldl
      (fun (acc : _root_.Std.HashMap NIdx Nat × Nat) e => (acc.1.insert e.1 acc.2, acc.2 + 1)) (S, k.val)).1 := by
  rw [index_of_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, v⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as i1, hi1
    have hv := cast_u64_val hi1
    peel h as ⟨_, idx1⟩, hidx1
    peel h as k1, hk1
    have ins := hs.insert (by rw [hv]; scalar_tac) hidx1
    have ih := index_of_loop_eq c ins k1 h
    rw [usize_succ hk1, hv] at ih
    rw [drop_cons_of_lt hi, ← he]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact hs
termination_by c.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- **`index_of` is `indexOf`.** -/
theorem index_of_eq {c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))} {o}
    (h : index_of c = ok o) : IdxRel o (Modular.indexOf (absC c)) := by
  rw [index_of] at h
  peel h as s, hs
  have := index_of_loop_eq c (IdxRel.empty hs) _ h
  simpa [Modular.indexOf] using this

theorem deps_of_loop0_loop0_eq {idx S} (hidx : IdxRel idx S)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    {d : alloc.vec.Vec Std.U64} (hd : FitsN d) (i : Std.Usize) {o}
    (h : deps_of_loop0_loop0 idx imps d i = ok o) :
    o.val.map (·.val) = d.val.map (·.val) ++
      ((imps.val.drop i.val).map absImp).filterMap (fun i => S[i.module]?) ∧ FitsN o := by
  rw [deps_of_loop0_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len imps
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    peel h as o1, ho1
    have e1 := idx_lookup_eq hidx ho1
    rw [idx_lookup] at ho1
    peel ho1 as o2, ho2
    have hfit := (hidx.get_eq ho2).2
    peel h as d1, hd1
    peel h as i2, hi2
    have hd1' : d1.val.map (·.val) = d.val.map (·.val) ++ (absOpt o1).toList ∧ FitsN d1 := by
      cases o1 with
      | none => cases Result.ok_injective hd1; simpa using hd
      | some j =>
        have hj : o2 = some j := by
          cases o2 <;> cases Result.ok_injective ho1; rfl
        have ev := ConRon.Refine.vec_push_val hd1
        refine ⟨by simp [ev], fun x hx => ?_⟩
        rw [ev] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hd x hx
        · simp at hx; rw [hx]; exact hfit j hj
    have ih := deps_of_loop0_loop0_eq hidx imps hd1'.2 i2 h
    rw [usize_succ hi2] at ih
    refine ⟨?_, ih.2⟩
    rw [ih.1, hd1'.1, drop_cons_of_lt hi, List.map_cons, List.filterMap_cons, List.append_assoc]
    congr 1
    simp only [absImp, absImportF] at e1 ⊢
    rw [← e1]
    cases o1 <;> rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨by simp, hd⟩
termination_by imps.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

theorem deps_of_loop0_eq {idx S} (hidx : IdxRel idx S)
    (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    {out : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hout : FitsD out) (k : Std.Usize) {o}
    (h : deps_of_loop0 idx c out k = ok o) :
    o.val.map absNat = out.val.map absNat ++
      ((c.val.drop k.val).map absNode).map (fun e => e.2.filterMap fun i => S[i.module]?) ∧ FitsD o := by
  rw [deps_of_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, imps⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as d1, hd1
    obtain ⟨e1, f1⟩ := deps_of_loop0_loop0_eq hidx imps (d := alloc.vec.Vec.with_capacity _ _)
      (fun x hx => by simp at hx) _ hd1
    peel h as out1, hout1
    peel h as k1, hk1
    have ev := ConRon.Refine.vec_push_val hout1
    have hf1 : FitsD out1 := fun d hd => by
      rw [ev] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hout d hd
      · simp at hd; subst hd; exact f1
    have ih := deps_of_loop0_eq hidx c hf1 k1 h
    rw [usize_succ hk1] at ih
    refine ⟨?_, ih.2⟩
    rw [ih.1, ev, drop_cons_of_lt hi, ← he]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    congr 2
    simp only [vec_with_capacity_val, List.map_nil, List.nil_append] at e1
    simp [absNat, e1, absImports]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨by simp, hout⟩
termination_by c.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- **`deps_of` is `depsOf`**, every position fitting a `usize`. -/
theorem deps_of_eq {idx S} (hidx : IdxRel idx S)
    {c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))} {o}
    (h : deps_of idx c = ok o) : absDeps o = Modular.depsOf S (absC c) ∧ FitsD o := by
  rw [deps_of] at h
  obtain ⟨e, f⟩ := deps_of_loop0_eq hidx c (out := alloc.vec.Vec.with_capacity _ _)
    (fun x hx => by simp at hx) _ h
  refine ⟨?_, f⟩
  simp only [vec_with_capacity_val, List.map_nil, List.nil_append] at e
  simp only [absDeps, e, Modular.depsOf, absC]
  simp [List.map_map, Function.comp_def]

/-! ## The verdict's searches -/

/-- The twin's rank function of two tables. -/
@[reducible] def absRk (S : _root_.Std.HashMap NIdx Nat) (rank : alloc.vec.Vec (Option Std.U64)) :
    NIdx → Option Nat :=
  Modular.rankOf S (absRanks rank)

theorem first_missing_root_loop_eq {pos P} (hpos : NSet pos P) (roots : alloc.vec.Vec arena.handle.NIdx)
    (r : Std.Usize) {o} (h : first_missing_root_loop pos roots r = ok o) :
    (o.bind fun r => roots.val[r.val]?).map absNIdx =
      ((roots.val.drop r.val).map absNIdx).find? (!P.contains ·) := by
  rw [first_missing_root_loop] at h
  by_cases hlt : r < alloc.vec.Vec.len roots
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hpos hb
    rw [drop_cons_of_lt hi, List.map_cons, List.find?_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as r1, hr1
      have ih := first_missing_root_loop_eq hpos roots r1 h
      rw [usize_succ hr1] at ih
      rw [← eb, cb]
      exact ih
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      rw [← eb]
      simp at cb
      simp [cb, hi]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by roots.val.length - r.val
decreasing_by have := lt_len hlt; rw [usize_succ hr1]; omega

theorem first_unranked_loop_eq {idx S} (hidx : IdxRel idx S)
    (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (rank : alloc.vec.Vec (Option Std.U64)) (k : Std.Usize) {o}
    (h : first_unranked_loop c idx rank k = ok o) :
    (o.bind fun k => c.val[k.val]?).map absNode =
      ((c.val.drop k.val).map absNode).find? (fun e => (absRk S rank e.1).isNone) := by
  rw [first_unranked_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, v⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as o1, ho1
    have e1 : absOpt o1 = absRk S rank (absNIdx n) := rank_of_eq hidx ho1
    rw [drop_cons_of_lt hi, List.map_cons, List.find?_cons, ← he]
    rw [← e1]
    simp only [core.option.Option.is_none] at h
    cases o1 with
    | none =>
      simp only [Option.isNone_none, ↓reduceIte] at h
      cases Result.ok_injective h
      simp [hi, ← he]
    | some x =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h
      peel h as k1, hk1
      have ih := first_unranked_loop_eq hidx c rank k1 h
      rw [usize_succ hk1] at ih
      simpa using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by c.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

theorem bad_edge_loop_eq {pos P idx S} (hpos : NSet pos P) (hidx : IdxRel idx S)
    (rank : alloc.vec.Vec (Option Std.U64)) (m : arena.handle.NIdx)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (i : Std.Usize) {o}
    (h : bad_edge_loop pos idx rank m imps i = ok o) :
    (o.bind fun i => imps.val[i.val]?).map absImp =
      ((imps.val.drop i.val).map absImp).find? (!Modular.edgeOk P (absRk S rank) (absNIdx m) ·) ∧
      ∀ j, o = some j → j.val < imps.val.length := by
  rw [bad_edge_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len imps
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    peel h as b, hb
    have eb := edge_ok_eq hpos hidx hb
    rw [drop_cons_of_lt hi, List.map_cons, List.find?_cons, ← eb]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as i2, hi2
      have ih := bad_edge_loop_eq hpos hidx rank m imps i2 h
      rw [usize_succ hi2] at ih
      rw [cb]
      exact ⟨ih.1, ih.2⟩
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      simp at cb
      exact ⟨by simp [cb, hi], fun j hj => by cases hj; exact hi⟩
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨rfl, fun _ h => by cases h⟩
termination_by imps.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

theorem find_not_none {α : Type} {q : α → Bool} {l : List α} :
    l.find? (fun x => !q x) = none ↔ l.all q = true := by
  simp [List.find?_eq_none, List.all_eq_true]

/-- The twin's edge fault of a node. -/
@[reducible] def edgeFault (P : _root_.Std.HashSet NIdx) (rk : NIdx → Option Nat) (e : Node) :
    NIdx × Option NIdx :=
  (e.1, (e.2.find? (!Modular.edgeOk P rk e.1 ·)).map (·.module))

theorem first_bad_node_loop_eq {pos P idx S} (hpos : NSet pos P) (hidx : IdxRel idx S)
    (rank : alloc.vec.Vec (Option Std.U64))
    (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))) (k : Std.Usize) {o}
    (h : first_bad_node_loop pos idx rank c k = ok o) :
    (o.bind fun p => c.val[p.1.val]?.bind fun e => e.2.val[p.2.val]?.map fun i => (e.1, i)).map
        (fun q => (absNIdx q.1, some (absNIdx q.2.module))) =
      (((c.val.drop k.val).map absNode).find? (fun e => !e.2.all (Modular.edgeOk P (absRk S rank) e.1))).map
        (edgeFault P (absRk S rank)) := by
  rw [first_bad_node_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, v⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as o1, ho1
    obtain ⟨e1, hb1⟩ := bad_edge_loop_eq hpos hidx rank n v _ ho1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
    rw [drop_cons_of_lt hi, List.map_cons, List.find?_cons, ← he]
    have ea : (absNode (n, v)).2.toList = v.val.map absImp := by simp
    cases o1 with
    | none =>
      dsimp only at h
      peel h as k1, hk1
      have ih := first_bad_node_loop_eq hpos hidx rank c k1 h
      rw [usize_succ hk1] at ih
      have hall : (absNode (n, v)).2.all (Modular.edgeOk P (absRk S rank) (absNode (n, v)).1) = true := by
        rw [← Array.all_toList, ea]
        exact find_not_none.mp e1.symm
      rw [hall]
      exact ih
    | some i =>
      dsimp only at h
      cases Result.ok_injective h
      simp only [Option.bind_some] at e1
      cases hv : v.val[i.val]? with
      | none => rw [List.getElem?_eq_none_iff] at hv; have := hb1 i rfl; omega
      | some x =>
        rw [hv] at e1
        have hall : (absNode (n, v)).2.all (Modular.edgeOk P (absRk S rank) (absNode (n, v)).1) = false := by
          rw [← Array.all_toList, ea]
          cases hq : (v.val.map absImp).all (Modular.edgeOk P (absRk S rank) (absNIdx n))
          · rfl
          · rw [← find_not_none] at hq; rw [hq] at e1; simp at e1
        rw [hall]
        have ef : (absNode (n, v)).2.find? (!Modular.edgeOk P (absRk S rank) (absNode (n, v)).1 ·) =
            some (absImp x) := by
          rw [← Array.find?_toList, ea]; exact e1.symm
        simp [edgeFault, ef, hi, ← he, hv, absImportF]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by c.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-! ## `ranks_distinct` -/

/-- The ranks' hash. -/
abbrev hW := U64.Insts.Con_ron_coreRonHashmapHashable
/-- The ranks' equality. -/
abbrev eW := U64.Insts.Con_ron_coreRonHashmapEq2

/-- **The ranks met**: the table of the present ones and the flag of the missing one, as upstream's
set of optional ranks. -/
structure SeenRel (m : ron.hashmap2.HashMap2 Std.U64 Bool) (none_seen : Bool)
    (T : _root_.Std.HashSet (Option Nat)) : Prop where
  inv : Inv hW m
  mem : ∀ r, (toFun m r).isSome = T.contains (some r.val)
  none : none_seen = T.contains none

theorem ranks_distinct_loop_eq {idx S} (hidx : IdxRel idx S)
    (c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (rank : alloc.vec.Vec (Option Std.U64)) {seen none_seen T} (hT : SeenRel seen none_seen T)
    (k : Std.Usize) {o} (h : ranks_distinct_loop c idx rank seen none_seen k = ok o) :
    o = ConLeche.Frontend.Olean.distinctGo (((c.val.drop k.val).map absNode).map fun e => absRk S rank e.1) T := by
  rw [ranks_distinct_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len c
  · rw [ite_eq_left hlt] at h
    peel h as ⟨n, v⟩, hp
    obtain ⟨hi, he⟩ := vec_index_eq hp
    peel h as o1, ho1
    have e1 : absOpt o1 = absRk S rank (absNIdx n) := rank_of_eq hidx ho1
    rw [drop_cons_of_lt hi, List.map_cons, List.map_cons, ← he]
    rw [← e1, ConLeche.Frontend.Olean.distinctGo]
    simp only [_root_.Std.HashSet.containsThenInsert_fst, _root_.Std.HashSet.containsThenInsert_snd]
    cases o1 with
    | none =>
      dsimp only at h
      simp only [absOpt, Option.map_none]
      rw [← hT.none]
      cases none_seen with
      | true => cases Result.ok_injective h; rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        peel h as k1, hk1
        have hT' : SeenRel seen true (T.insert none) := by
          refine ⟨hT.inv, fun r => ?_, by simp⟩
          rw [_root_.Std.HashSet.contains_insert, hT.mem r]; simp
        have ih := ranks_distinct_loop_eq hidx c rank hT' k1 h
        rw [usize_succ hk1] at ih
        simpa using ih
    | some r =>
      dsimp only at h
      peel h as b, hb
      have eb := ConRon.Refine.HashMap2.contains_key_refines_gen (P := fun _ => True)
        ConRon.Refine2.Frontend.u64Eq2Fwd hT.inv (fun _ _ => trivial) trivial hb
      rw [hT.mem r] at eb
      simp only [absOpt, Option.map_some]
      rw [← eb]
      cases b with
      | true => cases Result.ok_injective h; rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        peel h as ⟨_, seen1⟩, hs1
        peel h as k1, hk1
        obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen (P := fun _ => True)
          ConRon.Refine2.Frontend.u64Eq2Fwd hT.inv (fun _ _ => trivial) trivial hs1
        have hT' : SeenRel seen1 none_seen (T.insert (some r.val)) := by
          refine ⟨hinv, fun r1 => ?_, ?_⟩
          · rw [hupd, Function.update_apply, _root_.Std.HashSet.contains_insert]
            by_cases hr : r1 = r
            · subst hr; simp
            · have hne : (some r.val == some r1.val) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
                exact fun he => hr (UScalar.eq_of_val_eq he.symm)
              rw [ite_eq_right hr, hne, Bool.false_or]
              exact hT.mem r1
          · rw [_root_.Std.HashSet.contains_insert, hT.none]; simp
        have ih := ranks_distinct_loop_eq hidx c rank hT' k1 h
        rw [usize_succ hk1] at ih
        simpa using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by c.val.length - k.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hk1]; omega)

/-- **`ranks_distinct` is `distinctGo` on the ranks.** -/
theorem ranks_distinct_eq {idx S} (hidx : IdxRel idx S)
    {c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {rank : alloc.vec.Vec (Option Std.U64)} {o} (h : ranks_distinct c idx rank = ok o) :
    o = ConLeche.Frontend.Olean.distinctGo ((absC c).toList.map fun e => absRk S rank e.1) {} := by
  rw [ranks_distinct] at h
  peel h as seen, hseen
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hW) hseen
  have := ranks_distinct_loop_eq hidx c rank (T := {}) ⟨hinv, fun r => by rw [hnone]; simp, by simp⟩ _ h
  simpa using this

/-! ## `verdict` -/

/-- **`verdict` is `verdict`**, the rank function the twin's of the two tables. -/
theorem verdict_eq {roots : alloc.vec.Vec arena.handle.NIdx}
    {c : alloc.vec.Vec (arena.handle.NIdx ×
      alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {idx S} (hidx : IdxRel idx S) {rank : alloc.vec.Vec (Option Std.U64)} {o}
    (h : verdict roots c idx rank = ok o) :
    o.map absFault = Modular.verdict (roots.val.map absNIdx) (absC c).toList (absRk S rank) := by
  rw [verdict] at h
  peel h as pos, hpos
  have hP := names_of_eq hpos
  peel h as o0, ho0
  have e0 := first_missing_root_loop_eq hP roots _ ho0
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e0
  simp only [Modular.verdict]
  cases o0 with
  | some r =>
    dsimp only at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    cases Result.ok_injective h
    simp only [Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some] at e0
    rw [← e0]
    rfl
  | none =>
    dsimp only at h
    simp only [Option.bind_none, Option.map_none] at e0
    rw [← e0]
    dsimp only
    peel h as o1, ho1
    have e1 := first_unranked_loop_eq hidx c rank _ ho1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
    have ec : (absC c).toList = c.val.map absNode := by simp
    cases o1 with
    | some k =>
      dsimp only at h
      peel h as ⟨n, v⟩, hp
      obtain ⟨hi, he⟩ := vec_index_eq hp
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      cases Result.ok_injective h
      simp only [Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some, ← he] at e1
      rw [← e1]
      rfl
    | none =>
      dsimp only at h
      simp only [Option.bind_none, Option.map_none] at e1
      rw [← e1]
      dsimp only
      peel h as b, hb
      have eb := ranks_distinct_eq hidx hb
      rw [ec] at eb
      rw [← eb]
      by_cases cb : b = true
      · rw [ite_eq_left cb] at h
        rw [cb]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        peel h as o2, ho2
        have e2 := first_bad_node_loop_eq hP hidx rank c _ ho2
        simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e2
        cases o2 with
        | none =>
          cases Result.ok_injective h
          simp only [Option.bind_none, Option.map_none] at e2
          cases hf : (c.val.map absNode).find? (fun e => !e.2.all (Modular.edgeOk (Modular.namesOf (c.val.map absNode)) (absRk S rank) e.1)) with
          | none => rfl
          | some x =>
            rw [hf] at e2; cases e2
        | some q =>
          obtain ⟨e, i⟩ := q
          dsimp only at h
          peel h as ⟨n, v⟩, hp
          obtain ⟨hi, he⟩ := vec_index_eq hp
          peel h as n1, hn1
          cases nidx_dup2_ok hn1
          peel h as x, hx
          obtain ⟨hix, rfl⟩ := vec_index_eq hx
          peel h as n2, hn2
          cases nidx_dup2_ok hn2
          cases Result.ok_injective h
          simp only [Option.bind_some, List.getElem?_eq_getElem hi, ← he, List.getElem?_eq_getElem hix,
            Option.map_some] at e2
          cases hf : (c.val.map absNode).find? (fun e => !e.2.all (Modular.edgeOk (Modular.namesOf (c.val.map absNode)) (absRk S rank) e.1)) with
          | none => rw [hf] at e2; cases e2
          | some y =>
            rw [hf] at e2
            simp only [Option.map_some, Option.some.injEq] at e2
            obtain ⟨y1, y2⟩ := y
            simp only [edgeFault, Prod.mk.injEq] at e2
            obtain ⟨r1, r2⟩ := e2
            subst r1
            simp only [Option.map_some, absFault]
            rw [r2]
      · rw [ite_eq_right cb] at h
        cases Result.ok_injective h
        simp at cb
        rw [cb]
        rfl

end ConRon.Refine2.Modular

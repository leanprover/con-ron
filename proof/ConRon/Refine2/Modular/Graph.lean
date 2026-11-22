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

/-! ## Arrays, read and written -/

theorem range'_cons {k n : Nat} (h : k < n) : List.range' k (n - k) = k :: List.range' (k + 1) (n - (k + 1)) := by
  rw [show n - k = (n - (k + 1)) + 1 by omega]; rfl

theorem range'_nil {k n : Nat} (h : n ≤ k) : List.range' k (n - k) = [] := by
  rw [show n - k = 0 by omega]; rfl

theorem index_mut_ok {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, f)) :
    ∃ hi : i.val < v.val.length, x = v.val[i.val] ∧ f = alloc.vec.Vec.set v i := by
  obtain ⟨hx, hf⟩ := ConRon.Refine.ConsMap.vec_index_mut_iff.mp h
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hx
  exact ⟨hi, he.symm, hf⟩

theorem set_abs {α β : Type} (A : α → β) (v : alloc.vec.Vec α) (j : Std.Usize) (y : α) :
    ((alloc.vec.Vec.set v j y).val.map A).toArray = ((v.val.map A).toArray).set! j.val (A y) := by
  apply Array.toList_inj.mp
  simp [List.map_set]

theorem set!_oob {β : Type} (l : List β) (j : Nat) (y : β) (h : l.length ≤ j) :
    l.toArray.set! j y = l.toArray := by
  apply Array.toList_inj.mp
  simp [List.set_eq_of_length_le h]

theorem modify_abs {α β : Type} (A : α → β) (v : alloc.vec.Vec α) (j : Std.Usize) (y : α) (g : β → β)
    (hj : j.val < v.val.length) (hy : A y = g (A v.val[j.val])) :
    ((alloc.vec.Vec.set v j y).val.map A).toArray = ((v.val.map A).toArray).modify j.val g := by
  apply Array.toList_inj.mp
  rw [Array.toList_modify]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    simp [List.getElem_set]
    split <;> simp_all

theorem modify_oob {β : Type} (l : List β) (j : Nat) (g : β → β) (h : l.length ≤ j) :
    l.toArray.modify j g = l.toArray := by
  apply Array.toList_inj.mp
  rw [Array.toList_modify, List.toList_toArray, List.modify_eq_self h]

/-! ## `kahn_users` -/

theorem kahn_users_loop0_eq (n : Std.Usize) (users : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (k : Std.Usize) {o}
    (h : kahn_users_loop0 n users k = ok o) :
    o.val = users.val ++ List.replicate (n.val - k.val) (alloc.vec.Vec.new Std.U64) := by
  rw [kahn_users_loop0] at h
  by_cases hlt : k < n
  · rw [ite_eq_left hlt] at h
    peel h as u1, hu1
    peel h as k1, hk1
    have ih := kahn_users_loop0_eq n u1 k1 h
    have hlt' : k.val < n.val := hlt
    rw [ih, ConRon.Refine.vec_push_val hu1, usize_succ hk1, List.append_assoc,
      show n.val - k.val = (n.val - (k.val + 1)) + 1 by omega, List.replicate_succ]
    rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ k.val < n.val := hlt
    rw [show n.val - k.val = 0 by omega]; simp
termination_by n.val - k.val
decreasing_by have : k.val < n.val := hlt; rw [usize_succ hk1]; omega

theorem kahn_users_loop1_loop0_eq (users : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (x : Std.Usize)
    (d : alloc.vec.Vec Std.U64) (hd : FitsN d) (hu : FitsD users) (i : Std.Usize) {o}
    (h : kahn_users_loop1_loop0 users x d i = ok o) :
    absDeps o = ((d.val.drop i.val).map (·.val)).foldl (fun us j => us.modify j (·.push x.val)) (absDeps users) ∧
      FitsD o := by
  rw [kahn_users_loop1_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len d
  · rw [ite_eq_left hlt] at h
    peel h as i2, hi2
    obtain ⟨hi, rfl⟩ := vec_index_eq hi2
    peel h as j, hj
    have hjv := cast_usize_val (hd _ (List.getElem_mem hi)) hj
    peel h as u1, hu1
    peel h as i4, hi4
    have ih0 : absDeps u1 = (absDeps users).modify d.val[i.val].val (·.push x.val) ∧ FitsD u1 := by
      by_cases hjl : j < alloc.vec.Vec.len users
      · rw [ite_eq_left hjl] at hu1
        peel hu1 as ⟨v, back⟩, hv
        obtain ⟨hjb, rfl, rfl⟩ := index_mut_ok hv
        peel hu1 as i5, hi5
        have hx := cast_u64_val hi5
        peel hu1 as v1, hv1
        cases Result.ok_injective hu1
        have ev := ConRon.Refine.vec_push_val hv1
        refine ⟨?_, ?_⟩
        · rw [← hjv]
          apply modify_abs absNat users j v1 _ hjb
          simp [ev, hx]
        · intro e he
          rw [alloc.vec.Vec.set_val_eq] at he
          rcases List.mem_or_eq_of_mem_set he with he | he
          · exact hu e he
          · subst he
            intro z hz
            rw [ev] at hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hu _ (List.getElem_mem hjb) z hz
            · simp at hz; rw [hz, hx]; scalar_tac
      · rw [ite_eq_right hjl] at hu1
        cases Result.ok_injective hu1
        refine ⟨?_, hu⟩
        rw [modify_oob]
        have := not_lt_len hjl
        simp only [List.length_map]; omega
    have ih := kahn_users_loop1_loop0_eq u1 x d hd ih0.2 i4 h
    rw [usize_succ hi4] at ih
    rw [drop_cons_of_lt hi, List.map_cons, List.foldl_cons, ← ih0.1]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨rfl, hu⟩
termination_by d.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi4]; omega

theorem kahn_users_loop1_eq (deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (hd : FitsD deps) (n : Std.Usize)
    (hn : n.val = deps.val.length) (users : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (hu : FitsD users)
    (x : Std.Usize) {o} (h : kahn_users_loop1 deps n users x = ok o) :
    absDeps o = (List.range' x.val (n.val - x.val)).foldl (fun users x =>
      ((absDeps deps)[x]?.getD #[]).foldl (fun users j => users.modify j (·.push x)) users) (absDeps users) ∧
      FitsD o := by
  rw [kahn_users_loop1] at h
  by_cases hlt : x < n
  · rw [ite_eq_left hlt] at h
    have hlt' : x.val < n.val := hlt
    peel h as d, hd1
    obtain ⟨hi, rfl⟩ := vec_index_eq hd1
    peel h as u1, hu1
    obtain ⟨e1, f1⟩ := kahn_users_loop1_loop0_eq users x _ (hd _ (List.getElem_mem hi)) hu _ hu1
    peel h as x1, hx1
    have ih := kahn_users_loop1_eq deps hd n hn u1 f1 x1 h
    rw [usize_succ hx1] at ih
    rw [range'_cons hlt', List.foldl_cons]
    have eg : (absDeps deps)[x.val]?.getD #[] = absNat deps.val[x.val] := by simp [absDeps, hi]
    rw [eg]
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
    rw [show (absNat deps.val[x.val]).foldl (fun users j => users.modify j (·.push x.val)) (absDeps users)
      = absDeps u1 by rw [e1]; simp [absNat]]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ x.val < n.val := hlt
    rw [range'_nil (by omega)]
    exact ⟨rfl, hu⟩
termination_by n.val - x.val
decreasing_by rw [usize_succ hx1]; omega

/-- **`kahn_users` is `kahnUsers`.** -/
theorem kahn_users_eq {deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hd : FitsD deps) {o}
    (h : kahn_users deps = ok o) : absDeps o = Modular.kahnUsers (absDeps deps) ∧ FitsD o := by
  rw [kahn_users] at h
  peel h as u0, hu0
  have e0 := kahn_users_loop0_eq _ _ _ hu0
  have f0 : FitsD u0 := fun d hd' => by
    rw [e0] at hd'; simp at hd'; rw [hd'.2]; intro z hz; simp at hz
  obtain ⟨e, f⟩ := kahn_users_loop1_eq deps hd _ (vec_len_val deps) u0 f0 _ h
  refine ⟨?_, f⟩
  rw [e, Modular.kahnUsers, List.range_eq_range', vec_len_val]
  congr 1
  · simp only [absDeps, e0]
    simp [absNat]
  · simp

/-! ## `kahn` -/

theorem kahn_loop0_eq (deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (n : Std.Usize)
    (hn : n.val = deps.val.length) (wait q : alloc.vec.Vec Std.U64) (hq : FitsN q) (k : Std.Usize) {o}
    (h : kahn_loop0 deps n wait q k = ok o) :
    (absNat o.1, absNat o.2) = (List.range' k.val (n.val - k.val)).foldl
      (fun (acc : _root_.Array Nat × _root_.Array Nat) k =>
        let d := (absDeps deps)[k]?.getD #[]
        (acc.1.push d.size, if d.size == 0 then acc.2.push k else acc.2)) (absNat wait, absNat q) ∧
      FitsN o.2 := by
  rw [kahn_loop0] at h
  by_cases hlt : k < n
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < n.val := hlt
    peel h as v, hv
    obtain ⟨hi, rfl⟩ := vec_index_eq hv
    peel h as i1, hi1
    have e1 := cast_u64_val hi1
    peel h as wait1, hw1
    peel h as q1, hq1
    peel h as k1, hk1
    have eq1 : absNat q1 = (if (absNat deps.val[k.val]).size == 0 then (absNat q).push k.val else absNat q) ∧
        FitsN q1 := by
      by_cases h0 : alloc.vec.Vec.len deps.val[k.val] = 0#usize
      · rw [ite_eq_left h0] at hq1
        have hl : deps.val[k.val].val.length = 0 := by
          have := congrArg (·.val) h0; simpa [vec_len_val] using this
        peel hq1 as i3, hi3
        have e3 := cast_u64_val hi3
        have ev := ConRon.Refine.vec_push_val hq1
        refine ⟨by simp [absNat, hl, ev, e3], fun z hz => ?_⟩
        rw [ev] at hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hq z hz
        · simp at hz; rw [hz, e3]; scalar_tac
      · rw [ite_eq_right h0] at hq1
        cases Result.ok_injective hq1
        have hl : deps.val[k.val].val.length ≠ 0 := by
          intro hc; apply h0; apply UScalar.eq_of_val_eq; simpa [vec_len_val] using hc
        exact ⟨by simp [absNat, hl], hq⟩
    obtain ⟨ih, f⟩ := kahn_loop0_eq deps n hn wait1 q1 eq1.2 k1 h
    rw [usize_succ hk1] at ih
    refine ⟨?_, f⟩
    rw [ih, range'_cons hlt', List.foldl_cons]
    congr 1
    have eg : (absDeps deps)[k.val]?.getD #[] = absNat deps.val[k.val] := by simp [absDeps, hi]
    simp only [eg]
    rw [← eq1.1]
    congr 1
    simp [ConRon.Refine.vec_push_val hw1, e1, absNat]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ k.val < n.val := hlt
    rw [range'_nil (by omega)]
    exact ⟨rfl, hq⟩
termination_by n.val - k.val
decreasing_by have : k.val < n.val := hlt; rw [usize_succ hk1]; omega

theorem kahn_release_eq {wait q : alloc.vec.Vec Std.U64} (hq : FitsN q) {i1 : Std.U64} {y : Std.Usize}
    (hy : y.val = i1.val) {o}
    (h : (if y < alloc.vec.Vec.len wait then do
        let w ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U64) wait y
        let wait2 ← if w > 0#u64 then do
            let i3 ← w - 1#u64
            let (_, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U64) wait y
            ok (index_mut_back i3)
          else ok wait
        let v ← if w = 1#u64 then alloc.vec.Vec.push q i1 else ok q
        ok (wait2, v)
      else ok (wait, q)) = ok o) (hi1 : i1.val ≤ Std.Usize.max) :
    (absNat o.1, absNat o.2) = Modular.kahnRelease (absNat wait, absNat q) i1.val ∧ FitsN o.2 := by
  simp only [Modular.kahnRelease]
  by_cases hlt : y < alloc.vec.Vec.len wait
  · rw [ite_eq_left hlt] at h
    have hl := lt_len hlt
    rw [hy] at hl
    have hs : i1.val < (absNat wait).size := by simpa using hl
    rw [ite_eq_left hs]
    peel h as w, hw
    obtain ⟨hwi, rfl⟩ := vec_index_eq hw
    peel h as wait2, hw2
    peel h as v, hv
    cases Result.ok_injective h
    have ew : (absNat wait)[i1.val]! = wait.val[y.val].val := by
      rw [getElem!_pos (absNat wait) i1.val hs]; simp [absNat, hy]
    rw [ew]
    refine ⟨?_, ?_⟩
    · congr 1
      · by_cases hp : wait.val[y.val] > 0#u64
        · rw [ite_eq_left hp] at hw2
          have hp' : wait.val[y.val].val > 0 := hp
          rw [ite_eq_left hp']
          peel hw2 as i3, hi3
          peel hw2 as ⟨_, back⟩, hb
          obtain ⟨-, -, rfl⟩ := index_mut_ok hb
          cases Result.ok_injective hw2
          have e3 := ConRon.Refine.HashMap.uscalar_sub_eq hi3
          show ((alloc.vec.Vec.set wait y i3).val.map (·.val)).toArray = _
          rw [set_abs, ← hy, e3]
          rfl
        · rw [ite_eq_right hp] at hw2
          cases Result.ok_injective hw2
          have hp' : ¬ wait.val[y.val].val > 0 := hp
          rw [ite_eq_right hp']
      · by_cases h1 : wait.val[y.val] = 1#u64
        · rw [ite_eq_left h1] at hv
          have h1' : (wait.val[y.val].val == 1) = true := by simp [h1]
          rw [ite_eq_left h1']
          simp [ConRon.Refine.vec_push_val hv, absNat]
        · rw [ite_eq_right h1] at hv
          cases Result.ok_injective hv
          have h1' : ¬ (wait.val[y.val].val == 1) = true := by
            intro hc; apply h1; apply UScalar.eq_of_val_eq; simpa using hc
          rw [ite_eq_right h1']
    · by_cases h1 : wait.val[y.val] = 1#u64
      · rw [ite_eq_left h1] at hv
        intro z hz
        rw [ConRon.Refine.vec_push_val hv] at hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hq z hz
        · simp at hz; rw [hz]; exact hi1
      · rw [ite_eq_right h1] at hv
        cases Result.ok_injective hv
        exact hq
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hl := not_lt_len hlt
    rw [hy] at hl
    have hs : ¬ i1.val < (absNat wait).size := by simpa using hl
    rw [ite_eq_right hs]
    exact ⟨rfl, hq⟩

theorem kahn_loop1_loop0_eq (wait q us : alloc.vec.Vec Std.U64) (hq : FitsN q) (hus : FitsN us)
    (u : Std.Usize) {o} (h : kahn_loop1_loop0 wait q us u = ok o) :
    (absNat o.1, absNat o.2) = ((us.val.drop u.val).map (·.val)).foldl Modular.kahnRelease (absNat wait, absNat q) ∧
      FitsN o.2 := by
  rw [kahn_loop1_loop0] at h
  by_cases hlt : u < alloc.vec.Vec.len us
  · rw [ite_eq_left hlt] at h
    peel h as i1, hi1
    obtain ⟨hi, rfl⟩ := vec_index_eq hi1
    have hf := hus _ (List.getElem_mem hi)
    peel h as y, hy
    have hyv := cast_usize_val hf hy
    peel h as ⟨wait1, q1⟩, hq1
    peel h as u1, hu1
    obtain ⟨e1, f1⟩ := kahn_release_eq hq hyv hq1 hf
    obtain ⟨ih, f⟩ := kahn_loop1_loop0_eq wait1 q1 us f1 hus u1 h
    rw [usize_succ hu1] at ih
    refine ⟨?_, f⟩
    rw [ih, drop_cons_of_lt hi, List.map_cons, List.foldl_cons, ← e1]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨rfl, hq⟩
termination_by us.val.length - u.val
decreasing_by have := lt_len hlt; rw [usize_succ hu1]; omega

theorem kahn_loop1_eq (n : Std.Usize) (users : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (hu : FitsD users)
    (wait q : alloc.vec.Vec Std.U64) (hq : FitsN q) (i t : Std.Usize) {o}
    (h : kahn_loop1 n users wait q i t = ok o) :
    absNat o = Modular.kahnGo (absDeps users) (n.val - t.val) i.val (absNat wait) (absNat q) ∧ FitsN o := by
  rw [kahn_loop1] at h
  by_cases hlt : t < n
  · rw [ite_eq_left hlt] at h
    have hlt' : t.val < n.val := hlt
    rw [show n.val - t.val = (n.val - (t.val + 1)) + 1 by omega, Modular.kahnGo]
    by_cases hi : i < alloc.vec.Vec.len q
    · rw [ite_eq_left hi] at h
      have hi' := lt_len hi
      have hs : i.val < (absNat q).size := by simpa using hi'
      simp only [hs, ↓reduceDIte]
      peel h as i2, hi2
      obtain ⟨_hb, rfl⟩ := vec_index_eq hi2
      peel h as x, hx
      have hxv := cast_usize_val (hq _ (List.getElem_mem hi')) hx
      have eq : (absNat q)[i.val] = q.val[i.val].val := by simp [absNat]
      simp only [eq]
      by_cases hxl : x < alloc.vec.Vec.len users
      · rw [ite_eq_left hxl] at h
        have hxl' := lt_len hxl
        peel h as us, hus
        obtain ⟨_hb2, rfl⟩ := vec_index_eq hus
        peel h as ⟨wait1, q1⟩, hq1
        obtain ⟨e1, f1⟩ := kahn_loop1_loop0_eq wait q _ hq (hu _ (List.getElem_mem hxl')) _ hq1
        simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
        peel h as i4, hi4
        peel h as t1, ht1
        obtain ⟨ih, f⟩ := kahn_loop1_eq n users hu wait1 q1 f1 i4 t1 h
        rw [usize_succ hi4, usize_succ ht1] at ih
        refine ⟨?_, f⟩
        have eg : (absDeps users)[q.val[i.val].val]?.getD #[] = absNat users.val[x.val] := by
          rw [← hxv]; simp [absDeps, hxl']
        rw [eg, ih]
        have : (absNat users.val[x.val]).foldl Modular.kahnRelease (absNat wait, absNat q) =
            (absNat wait1, absNat q1) := by rw [e1]; simp [absNat]
        rw [this]
      · rw [ite_eq_right hxl] at h
        peel h as i4, hi4
        peel h as t1, ht1
        obtain ⟨ih, f⟩ := kahn_loop1_eq n users hu wait q hq i4 t1 h
        rw [usize_succ hi4, usize_succ ht1] at ih
        refine ⟨?_, f⟩
        have eg : (absDeps users)[q.val[i.val].val]?.getD #[] = #[] := by
          have := not_lt_len hxl
          rw [hxv] at this
          rw [Array.getElem?_eq_none (by simpa using this)]
          rfl
        rw [eg, ih]
        rfl
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      have hs : ¬ i.val < (absNat q).size := by simpa using not_lt_len hi
      simp only [hs, ↓reduceDIte]
      exact ⟨trivial, hq⟩
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ t.val < n.val := hlt
    rw [show n.val - t.val = 0 by omega, Modular.kahnGo]
    exact ⟨rfl, hq⟩
termination_by n.val - t.val
decreasing_by all_goals (rw [usize_succ ht1]; omega)

/-- **`kahn` is `kahn`**, every position of the order fitting a `usize`. -/
theorem kahn_eq {deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hd : FitsD deps) {o}
    (h : kahn deps = ok o) : absNat o = Modular.kahn (absDeps deps) ∧ FitsN o := by
  rw [kahn] at h
  peel h as users, hus
  obtain ⟨eu, fu⟩ := kahn_users_eq hd hus
  peel h as ⟨wait1, q⟩, hq
  obtain ⟨e0, f0⟩ := kahn_loop0_eq deps _ (vec_len_val deps) _ _ (fun z hz => by simp at hz) _ hq
  obtain ⟨e, f⟩ := kahn_loop1_eq _ users fu wait1 q f0 _ _ h
  refine ⟨?_, f⟩
  rw [e, Modular.kahn, Modular.kahnStart, ← eu, List.range_eq_range']
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero, vec_len_val] at e0 ⊢
  have es : (absDeps deps).size = deps.val.length := by simp
  rw [es]
  simp only [vec_with_capacity_val, vec_new_val, List.map_nil, absNat] at e0
  rw [← e0]

/-! ## `ranks_of` -/

theorem u64_succ {k k1 : Std.U64} (h : k + 1#u64 = ok k1) : k1.val = k.val + 1 := by
  rw [ConRon.Refine.Nat.uadd_val h]; rfl

theorem ranks_of_loop0_eq (n : Std.U64) (rank : alloc.vec.Vec (Option Std.U64)) (k : Std.U64) {o}
    (h : ranks_of_loop0 n rank k = ok o) :
    o.val = rank.val ++ List.replicate (n.val - k.val) none := by
  rw [ranks_of_loop0] at h
  by_cases hlt : k < n
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < n.val := hlt
    peel h as r1, hr1
    peel h as k1, hk1
    have ih := ranks_of_loop0_eq n r1 k1 h
    rw [ih, ConRon.Refine.vec_push_val hr1, u64_succ hk1, List.append_assoc,
      show n.val - k.val = (n.val - (k.val + 1)) + 1 by omega, List.replicate_succ]
    rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ k.val < n.val := hlt
    rw [show n.val - k.val = 0 by omega]; simp
termination_by n.val - k.val
decreasing_by have : k.val < n.val := hlt; rw [u64_succ hk1]; omega

theorem ranks_of_loop1_eq (ord : alloc.vec.Vec Std.U64) (hord : FitsN ord) (rank : alloc.vec.Vec (Option Std.U64))
    (t : Std.Usize) {o} (h : ranks_of_loop1 ord rank t = ok o) :
    absRanks o = (List.range' t.val (ord.val.length - t.val)).foldl
      (fun r t => r.set! ((absNat ord)[t]?.getD 0) (some t)) (absRanks rank) := by
  rw [ranks_of_loop1] at h
  by_cases hlt : t < alloc.vec.Vec.len ord
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as i1, hi1
    obtain ⟨_hb, rfl⟩ := vec_index_eq hi1
    peel h as p, hp
    have hpv := cast_usize_val (hord _ (List.getElem_mem hlt')) hp
    peel h as r1, hr1
    peel h as t1, ht1
    have ih := ranks_of_loop1_eq ord hord r1 t1 h
    rw [usize_succ ht1] at ih
    have eg : (absNat ord)[t.val]?.getD 0 = p.val := by simp [absNat, hlt', hpv]
    have er : absRanks r1 = (absRanks rank).set! p.val (some t.val) := by
      by_cases hpl : p < alloc.vec.Vec.len rank
      · rw [ite_eq_left hpl] at hr1
        peel hr1 as i3, hi3
        have e3 := cast_u64_val hi3
        peel hr1 as ⟨_, back⟩, hb
        obtain ⟨_, _, rfl⟩ := index_mut_ok hb
        cases Result.ok_injective hr1
        show ((alloc.vec.Vec.set rank p (some i3)).val.map absOpt).toArray = _
        rw [set_abs]; simp [e3]
      · rw [ite_eq_right hpl] at hr1
        cases Result.ok_injective hr1
        rw [set!_oob]
        have := not_lt_len hpl
        simpa using this
    rw [range'_cons hlt', List.foldl_cons, eg, ← er]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [range'_nil (not_lt_len hlt)]
    rfl
termination_by ord.val.length - t.val
decreasing_by have := lt_len hlt; rw [usize_succ ht1]; omega

/-- **`ranks_of` is `ranksOf`.** -/
theorem ranks_of_eq {n : Std.U64} {ord : alloc.vec.Vec Std.U64} (hord : FitsN ord) {o}
    (h : ranks_of n ord = ok o) : absRanks o = Modular.ranksOf n.val (absNat ord) := by
  rw [ranks_of] at h
  peel h as i, -
  peel h as r1, hr1
  have e0 := ranks_of_loop0_eq _ _ _ hr1
  have e := ranks_of_loop1_eq ord hord r1 _ h
  rw [e, Modular.ranksOf, List.range_eq_range']
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero]
  have es : (absNat ord).size = ord.val.length := by simp
  rw [es]
  congr 1
  simp only [absRanks, e0]
  simp

/-! ## `done_of`, `cycle_start`, `cycle_next`, `cycle_step` -/

/-- The marks, as the twin's. -/
@[reducible] def absDone (v : alloc.vec.Vec Bool) : _root_.Array Bool := v.val.toArray

theorem set_done (v : alloc.vec.Vec Bool) (j : Std.Usize) (y : Bool) :
    (alloc.vec.Vec.set v j y).val.toArray = (v.val.toArray).set! j.val y := by
  apply Array.toList_inj.mp
  simp

theorem done_of_loop0_eq (n : Std.Usize) (done : alloc.vec.Vec Bool) (k : Std.Usize) {o}
    (h : done_of_loop0 n done k = ok o) :
    o.val = done.val ++ List.replicate (n.val - k.val) false := by
  rw [done_of_loop0] at h
  by_cases hlt : k < n
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < n.val := hlt
    peel h as d1, hd1
    peel h as k1, hk1
    have ih := done_of_loop0_eq n d1 k1 h
    rw [ih, ConRon.Refine.vec_push_val hd1, usize_succ hk1, List.append_assoc,
      show n.val - k.val = (n.val - (k.val + 1)) + 1 by omega, List.replicate_succ]
    rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ k.val < n.val := hlt
    rw [show n.val - k.val = 0 by omega]; simp
termination_by n.val - k.val
decreasing_by have : k.val < n.val := hlt; rw [usize_succ hk1]; omega

theorem done_of_loop1_eq (ord : alloc.vec.Vec Std.U64) (hord : FitsN ord) (done : alloc.vec.Vec Bool)
    (j : Std.Usize) {o} (h : done_of_loop1 ord done j = ok o) :
    absDone o = ((ord.val.drop j.val).map (·.val)).foldl (fun d p => d.set! p true) (absDone done) := by
  rw [done_of_loop1] at h
  by_cases hlt : j < alloc.vec.Vec.len ord
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as i1, hi1
    obtain ⟨_hb, rfl⟩ := vec_index_eq hi1
    peel h as p, hp
    have hpv := cast_usize_val (hord _ (List.getElem_mem hlt')) hp
    peel h as d1, hd1
    peel h as j1, hj1
    have ih := done_of_loop1_eq ord hord d1 j1 h
    rw [usize_succ hj1] at ih
    have er : absDone d1 = (absDone done).set! p.val true := by
      by_cases hpl : p < alloc.vec.Vec.len done
      · rw [ite_eq_left hpl] at hd1
        peel hd1 as ⟨_, back⟩, hb
        obtain ⟨_, _, rfl⟩ := index_mut_ok hb
        cases Result.ok_injective hd1
        exact set_done done p true
      · rw [ite_eq_right hpl] at hd1
        cases Result.ok_injective hd1
        rw [set!_oob]
        exact not_lt_len hpl
    rw [drop_cons_of_lt hlt', List.map_cons, List.foldl_cons, ← hpv, ← er]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by ord.val.length - j.val
decreasing_by have := lt_len hlt; rw [usize_succ hj1]; omega

/-- **`done_of` is `doneOf`.** -/
theorem done_of_eq {n : Std.Usize} {ord : alloc.vec.Vec Std.U64} (hord : FitsN ord) {o}
    (h : done_of n ord = ok o) : absDone o = Modular.doneOf n.val (absNat ord) := by
  rw [done_of] at h
  peel h as d1, hd1
  have e0 := done_of_loop0_eq _ _ _ hd1
  have e := done_of_loop1_eq ord hord d1 _ h
  rw [e, Modular.doneOf]
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero, absDone, e0]
  simp [absNat]

theorem cycle_start_loop_eq (n : Std.Usize) (done : alloc.vec.Vec Bool) (k : Std.Usize) {o}
    (h : cycle_start_loop n done k = ok o) :
    o.map (·.val) = (List.range' k.val (n.val - k.val)).find? fun k => !((absDone done)[k]?.getD false) := by
  rw [cycle_start_loop] at h
  by_cases hlt : k < n
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < n.val := hlt
    peel h as b, hb
    obtain ⟨hb1, rfl⟩ := vec_index_eq hb
    rw [range'_cons hlt', List.find?_cons]
    have eg : (absDone done)[k.val]?.getD false = done.val[k.val] := by simp [hb1]
    rw [eg]
    by_cases cb : done.val[k.val] = true
    · rw [ite_eq_left cb] at h
      peel h as k1, hk1
      have ih := cycle_start_loop_eq n done k1 h
      rw [usize_succ hk1] at ih
      rw [cb]; exact ih
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      simp at cb; simp [cb]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ k.val < n.val := hlt
    rw [range'_nil (by omega)]; rfl
termination_by n.val - k.val
decreasing_by rw [usize_succ hk1]; omega

/-- **`cycle_start` is `cycleStart`.** -/
theorem cycle_start_eq {n : Std.Usize} {done : alloc.vec.Vec Bool} {o}
    (h : cycle_start n done = ok o) : o.map (·.val) = Modular.cycleStart n.val (absDone done) := by
  have := cycle_start_loop_eq n done _ h
  simpa [Modular.cycleStart, List.range_eq_range'] using this

theorem cycle_next_loop_eq (done : alloc.vec.Vec Bool) (d : alloc.vec.Vec Std.U64) (hd : FitsN d)
    (i : Std.Usize) {o} (h : cycle_next_loop done d i = ok o) :
    o.map (·.val) = ((d.val.drop i.val).map (·.val)).find? fun y => !((absDone done)[y]?.getD false) := by
  rw [cycle_next_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len d
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as i2, hi2
    obtain ⟨_hb, rfl⟩ := vec_index_eq hi2
    peel h as y, hy
    have hyv := cast_usize_val (hd _ (List.getElem_mem hlt')) hy
    rw [drop_cons_of_lt hlt', List.map_cons, List.find?_cons, ← hyv]
    by_cases hyl : y < alloc.vec.Vec.len done
    · rw [ite_eq_left hyl] at h
      peel h as b, hb
      obtain ⟨hb1, rfl⟩ := vec_index_eq hb
      have eg : (absDone done)[y.val]?.getD false = done.val[y.val] := by simp [hb1]
      rw [eg]
      by_cases cb : done.val[y.val] = true
      · rw [ite_eq_left cb] at h
        peel h as i4, hi4
        have ih := cycle_next_loop_eq done d hd i4 h
        rw [usize_succ hi4] at ih
        rw [cb]; exact ih
      · rw [ite_eq_right cb] at h
        cases Result.ok_injective h
        simp at cb; simp [cb]
    · rw [ite_eq_right hyl] at h
      cases Result.ok_injective h
      have : (absDone done)[y.val]? = none := by
        have := not_lt_len hyl; simp; omega
      simp [this]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by d.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi4]; omega

/-- **`cycle_next` is `cycleNext`.** -/
theorem cycle_next_eq {deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hd : FitsD deps)
    {done : alloc.vec.Vec Bool} {x : Std.Usize} {o} (h : cycle_next deps done x = ok o) :
    o.map (·.val) = Modular.cycleNext (absDeps deps) (absDone done) x.val := by
  rw [cycle_next] at h
  simp only [Modular.cycleNext]
  by_cases hlt : x < alloc.vec.Vec.len deps
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as d, hd1
    obtain ⟨_hb, rfl⟩ := vec_index_eq hd1
    have := cycle_next_loop_eq done _ (hd _ (List.getElem_mem hlt')) _ h
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    rw [this]
    simp [absDeps, hlt', absNat]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : (absDeps deps)[x.val]? = none := by
      have := not_lt_len hlt; simp; omega
    simp [this]

/-- A step of the cycle's walk, as the twin's. -/
def absCS : frontend.modular.graph.CycleStep → Modular.CycleStep
  | .Repeat p => .repeat p.val
  | .Next o => .next (o.map (·.val))

/-- Every visit's place fits a `usize`. -/
def FitsO (v : alloc.vec.Vec (Option Std.U64)) : Prop := ∀ p, some p ∈ v.val → p.val ≤ Std.Usize.max

/-- **`cycle_step` is `cycleStep`.** -/
theorem cycle_step_eq {deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hd : FitsD deps)
    {done : alloc.vec.Vec Bool} {at_ : alloc.vec.Vec (Option Std.U64)} (hat : FitsO at_)
    {path : alloc.vec.Vec Std.U64} {x : Std.Usize} {o}
    (h : cycle_step deps done at_ path x = ok o) :
    (absCS o.1, absRanks o.2.1, absNat o.2.2) =
      Modular.cycleStep (absDeps deps) (absDone done) (absRanks at_) (absNat path) x.val ∧
      FitsO o.2.1 ∧ ∀ p, o.1 = .Repeat p → p.val ≤ Std.Usize.max := by
  rw [cycle_step] at h
  simp only [Modular.cycleStep]
  by_cases hlt : x < alloc.vec.Vec.len at_
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as o1, ho1
    obtain ⟨_hb, rfl⟩ := vec_index_eq ho1
    have eg : (absRanks at_)[x.val]? = some (absOpt at_.val[x.val]) := by simp [hlt']
    rw [eg]
    cases hx : at_.val[x.val] with
    | some p =>
      rw [hx] at h
      cases Result.ok_injective h
      have hp : p.val ≤ Std.Usize.max := hat p (by rw [← hx]; exact List.getElem_mem hlt')
      exact ⟨rfl, hat, fun q hq => by cases hq; exact hp⟩
    | none =>
      rw [hx] at h
      dsimp only at h
      peel h as i2, hi2
      have e2 := cast_u64_val hi2
      peel h as ⟨_, back⟩, hb
      obtain ⟨_, _, rfl⟩ := index_mut_ok hb
      peel h as i3, hi3
      have e3 := cast_u64_val hi3
      peel h as path1, hp1
      peel h as o2, ho2
      have en := cycle_next_eq hd ho2
      cases Result.ok_injective h
      have ea : absRanks (alloc.vec.Vec.set at_ x (some i2)) =
          (absRanks at_).set! x.val (some (absNat path).size) := by
        show ((alloc.vec.Vec.set at_ x (some i2)).val.map absOpt).toArray = _
        rw [set_abs]; simp [e2]
      have ep : absNat path1 = (absNat path).push x.val := by
        simp [ConRon.Refine.vec_push_val hp1, e3]
      refine ⟨?_, ?_, fun q hq => by cases hq⟩
      · simp only [absCS, en, ea, ep]
        rfl
      · intro q hq
        rw [alloc.vec.Vec.set_val_eq] at hq
        rcases List.mem_or_eq_of_mem_set hq with hq | hq
        · exact hat q hq
        · cases hq; rw [e2]; exact vec_len_le path
  · rw [ite_eq_right hlt] at h
    have : (absRanks at_)[x.val]? = none := by
      have := not_lt_len hlt; simp; omega
    rw [this]
    dsimp only
    peel h as i1, hi1
    have e1 := cast_u64_val hi1
    peel h as path1, hp1
    peel h as o2, ho2
    have en := cycle_next_eq hd ho2
    cases Result.ok_injective h
    refine ⟨?_, hat, fun q hq => by cases hq⟩
    simp [absCS, en, ConRon.Refine.vec_push_val hp1, e1]

/-! ## `path_from`, `cycle_of` -/

theorem path_from_loop_eq (path out : alloc.vec.Vec Std.U64) (i : Std.Usize) {o}
    (h : path_from_loop path out i = ok o) : o.val = out.val ++ path.val.drop i.val := by
  rw [path_from_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len path
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as i2, hi2
    obtain ⟨_hb, rfl⟩ := vec_index_eq hi2
    peel h as out1, ho1
    peel h as i3, hi3
    have ih := path_from_loop_eq path out1 i3 h
    rw [usize_succ hi3, ConRon.Refine.vec_push_val ho1] at ih
    rw [ih, drop_cons_of_lt hlt']
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by path.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi3]; omega

/-- **`path_from` is `path.extract p path.size`.** -/
theorem path_from_eq {path : alloc.vec.Vec Std.U64} {p : Std.Usize} {o} (h : path_from path p = ok o) :
    absNat o = (absNat path).extract p.val (absNat path).size := by
  have := path_from_loop_eq path _ p h
  apply Array.toList_inj.mp
  simp [this, List.extract_eq_take_drop, List.map_drop]

theorem cycle_of_loop0_eq (n : Std.Usize) (at_ : alloc.vec.Vec (Option Std.U64)) (a : Std.Usize) {o}
    (h : cycle_of_loop0 n at_ a = ok o) :
    o.val = at_.val ++ List.replicate (n.val - a.val) none := by
  rw [cycle_of_loop0] at h
  by_cases hlt : a < n
  · rw [ite_eq_left hlt] at h
    have hlt' : a.val < n.val := hlt
    peel h as d1, hd1
    peel h as a1, ha1
    have ih := cycle_of_loop0_eq n d1 a1 h
    rw [ih, ConRon.Refine.vec_push_val hd1, usize_succ ha1, List.append_assoc,
      show n.val - a.val = (n.val - (a.val + 1)) + 1 by omega, List.replicate_succ]
    rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ a.val < n.val := hlt
    rw [show n.val - a.val = 0 by omega]; simp
termination_by n.val - a.val
decreasing_by have : a.val < n.val := hlt; rw [usize_succ ha1]; omega

theorem cycle_of_loop1_fin (deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (n : Std.Usize)
    (done : alloc.vec.Vec Bool) (path : alloc.vec.Vec Std.U64) (at_ : alloc.vec.Vec (Option Std.U64))
    (x : Std.Usize) (rep : Option Std.U64) (t : Std.Usize) {o}
    (h : cycle_of_loop1 deps n done path at_ x rep true t = ok o) : o = (path, rep) := by
  rw [cycle_of_loop1] at h
  peel h as i, -
  by_cases hlt : t < i
  · rw [ite_eq_left hlt] at h
    exact (Result.ok_injective h).symm
  · rw [ite_eq_right hlt] at h
    exact (Result.ok_injective h).symm

theorem cycle_of_loop1_eq (deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (hd : FitsD deps) (n : Std.Usize)
    (done : alloc.vec.Vec Bool) (path : alloc.vec.Vec Std.U64) (at_ : alloc.vec.Vec (Option Std.U64))
    (hat : FitsO at_) (x : Std.Usize) (t : Std.Usize) {o}
    (h : cycle_of_loop1 deps n done path at_ x none false t = ok o) :
    (absOpt o.2, absNat o.1) =
      Modular.cycleWalk (absDeps deps) (absDone done) (n.val + 1 - t.val) (absRanks at_) (absNat path) x.val ∧
      ∀ p, o.2 = some p → p.val ≤ Std.Usize.max := by
  rw [cycle_of_loop1] at h
  peel h as i, hi
  have hiv := usize_succ hi
  by_cases hlt : t < i
  · rw [ite_eq_left hlt] at h
    have hlt' : t.val < n.val + 1 := by have : t.val < i.val := hlt; omega
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    peel h as ⟨cs, at1, path1⟩, hcs
    obtain ⟨ecs, fat1, frep⟩ := cycle_step_eq hd hat hcs
    rw [show n.val + 1 - t.val = (n.val + 1 - (t.val + 1)) + 1 by omega, Modular.cycleWalk]
    dsimp only at ecs
    rw [← ecs]
    peel h as ⟨x1, rep1, fin1, at2, path2⟩, hq
    peel h as t1, ht1
    cases cs with
    | Repeat p =>
      cases Result.ok_injective hq
      have := cycle_of_loop1_fin deps n done _ _ _ _ _ h
      subst this
      exact ⟨rfl, fun q hq => by cases hq; exact frep p rfl⟩
    | Next on =>
      cases on with
      | none =>
        simp only [bind_ok] at hq
        have e := Result.ok_injective hq
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
        have := cycle_of_loop1_fin deps n done _ _ _ _ _ h
        subst this
        exact ⟨rfl, fun q hq => by cases hq⟩
      | some y =>
        simp only [bind_ok] at hq
        have e := Result.ok_injective hq
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
        obtain ⟨ih, f⟩ := cycle_of_loop1_eq deps hd n done path1 at1 fat1 y t1 h
        rw [usize_succ ht1] at ih
        exact ⟨ih, f⟩
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : ¬ t.val < i.val := hlt
    rw [show n.val + 1 - t.val = 0 by omega, Modular.cycleWalk]
    exact ⟨rfl, fun q hq => by cases hq⟩
termination_by n.val + 1 - t.val
decreasing_by rw [usize_succ ht1]; omega

/-- **`cycle_of` is `cycleOf`.** -/
theorem cycle_of_eq {deps : alloc.vec.Vec (alloc.vec.Vec Std.U64)} (hd : FitsD deps)
    {ord : alloc.vec.Vec Std.U64} (hord : FitsN ord) {o} (h : cycle_of deps ord = ok o) :
    o.map (fun v => (absNat v).toList) = Modular.cycleOf (absDeps deps) (absNat ord) := by
  rw [cycle_of] at h
  peel h as done, hdone
  have edone := done_of_eq hord hdone
  peel h as s0, hs0
  have es := cycle_start_eq hs0
  have hn : (absDeps deps).size = (alloc.vec.Vec.len deps).val := by simp
  simp only [Modular.cycleOf, hn, ← edone, ← es]
  cases s0 with
  | none => cases Result.ok_injective h; rfl
  | some s =>
    dsimp only at h
    peel h as at1, hat1
    have eat := cycle_of_loop0_eq _ _ _ hat1
    have fat : FitsO at1 := fun p hp => by
      rw [eat] at hp; simp at hp
    peel h as ⟨path, rep⟩, hw
    obtain ⟨ew, frep⟩ := cycle_of_loop1_eq deps hd _ done _ at1 fat s _ hw
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero] at ew
    have eat' : absRanks at1 = Array.replicate (alloc.vec.Vec.len deps).val none := by
      simp only [absRanks, eat]; simp
    rw [eat'] at ew
    simp only [Option.map_some]
    rw [show (#[] : _root_.Array Nat) = absNat (alloc.vec.Vec.new Std.U64) by simp, ← ew]
    cases rep with
    | none => cases Result.ok_injective h; rfl
    | some p =>
      peel h as i, hi
      have hiv := cast_usize_val (frep p rfl) hi
      peel h as v, hv
      cases Result.ok_injective h
      simp only [absOpt, Option.map_some, Option.map_some, Option.some.injEq]
      have ep := path_from_eq hv
      rw [hiv] at ep
      rw [← ep]

/-! ## `expand` -/

/-- Handles, as the twin's. -/
@[reducible] def absNs (v : alloc.vec.Vec arena.handle.NIdx) : _root_.Array NIdx := (v.val.map absNIdx).toArray

theorem expand_loop0_loop0_eq {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {S : _root_.Std.HashSet NIdx}
    (hs : NSet seen S) (next : alloc.vec.Vec arena.handle.NIdx)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (k : Std.Usize) {o}
    (h : expand_loop0_loop0 seen next imps k = ok o) :
    let r := ((imps.val.drop k.val).map absImp).foldl (fun (sn : _root_.Std.HashSet NIdx × _root_.Array NIdx) i =>
      if sn.1.contains i.module then (sn.1, sn.2) else (sn.1.insert i.module, sn.2.push i.module))
      (S, absNs next)
    NSet o.1 r.1 ∧ absNs o.2 = r.2 := by
  rw [expand_loop0_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len imps
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as x, hx
    obtain ⟨_hb, rfl⟩ := vec_index_eq hx
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [drop_cons_of_lt hlt', List.map_cons, List.foldl_cons]
    peel h as ⟨s1, n1⟩, hq
    peel h as k1, hk1
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hq
      cases Result.ok_injective hq
      have ih := expand_loop0_loop0_eq hs next imps k1 h
      rw [usize_succ hk1] at ih
      rw [ite_eq_left (by rw [eb] at cb; exact cb)]
      exact ih
    · rw [ite_eq_right cb] at hq
      peel hq as d1, hd1
      cases nidx_dup2_ok hd1
      peel hq as ⟨_, s2⟩, hs2
      peel hq as d2, hd2
      cases nidx_dup2_ok hd2
      peel hq as n2, hn2
      have ea : absNs n2 = (absNs next).push (absNIdx imps.val[k.val].module) := by
        simp [absNs, ConRon.Refine.vec_push_val hn2]
      have hs2' := SetRel.insert nidx_eq2 absNIdx_inj hs hs2
      cases Result.ok_injective hq
      have ih := expand_loop0_loop0_eq hs2' _ imps k1 h
      rw [usize_succ hk1] at ih
      rw [ite_eq_right (by rw [eb] at cb; simpa [absImp, absImportF] using cb)]
      simp only [absImp, absImportF] at ih ⊢
      rw [← ea]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨hs, rfl⟩
termination_by imps.val.length - k.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hk1]; omega)

theorem expand_loop0_eq (pk : frontend.olean.spec.OleanPins)
    {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {S : _root_.Std.HashSet NIdx} (hs : NSet seen S)
    (out : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (next : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (i : Std.Usize) {o} (h : expand_loop0 pk seen out next rs i = ok o) :
    let r := Modular.expand S (absC out) (absNs next) ((rs.val.drop i.val).map absNode)
    NSet o.1 r.1 ∧ absC o.2.1 = r.2.1 ∧ absNs o.2.2 = r.2.2 := by
  rw [expand_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len rs
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as ⟨n0, imps⟩, hp
    obtain ⟨_hb, he⟩ := vec_index_eq hp
    peel h as ⟨seen1, next1⟩, hq
    obtain ⟨e1, e2⟩ := expand_loop0_loop0_eq hs next imps _ hq
    peel h as ⟨p, back⟩, hb
    obtain ⟨_hb2, rfl, rfl⟩ := index_mut_ok hb
    peel h as n, hn
    peel h as out1, ho1
    peel h as i2, hi2
    simp only at h
    have ih := expand_loop0_eq pk e1 out1 next1 _ i2 h
    rw [usize_succ hi2] at ih
    have hd : (alloc.vec.Vec.set rs i (n, alloc.vec.Vec.new _)).val.drop (i.val + 1) = rs.val.drop (i.val + 1) := by
      rw [alloc.vec.Vec.set_val_eq]; simp [List.drop_set]
    rw [hd] at ih
    have eo : absC out1 = (absC out).push (absNode (n0, imps)) := by
      simp [absC, ConRon.Refine.vec_push_val ho1, ← he]
    rw [eo] at ih
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1 e2
    rw [drop_cons_of_lt hlt', List.map_cons, ← he]
    simp only [Modular.expand]
    have ei : (absImports imps).foldl (fun (sn : _root_.Std.HashSet NIdx × _root_.Array NIdx) i =>
        if sn.1.contains i.module then (sn.1, sn.2) else (sn.1.insert i.module, sn.2.push i.module))
        (S, absNs next) = ((imps.val.map absImp).foldl (fun (sn : _root_.Std.HashSet NIdx × _root_.Array NIdx) i =>
        if sn.1.contains i.module then (sn.1, sn.2) else (sn.1.insert i.module, sn.2.push i.module))
        (S, absNs next)) := by
      rw [← Array.foldl_toList]
    rw [ei]
    rw [← e2]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨hs, rfl, rfl⟩
termination_by rs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; simp; omega

/-- **`expand` is `expand`.** -/
theorem expand_eq (pk : frontend.olean.spec.OleanPins)
    {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {S : _root_.Std.HashSet NIdx} (hs : NSet seen S)
    {out : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {next : alloc.vec.Vec arena.handle.NIdx}
    {rs : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {o} (h : expand pk seen out next rs = ok o) :
    let r := Modular.expand S (absC out) (absNs next) (rs.val.map absNode)
    NSet o.1 r.1 ∧ absC o.2.1 = r.2.1 ∧ absNs o.2.2 = r.2.2 := by
  have := expand_loop0_eq pk hs out next rs _ h
  simpa using this

/-! ## The header reads -/

theorem hdr_of_loop_eq (imps x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    (i : Std.Usize) {o} (h : hdr_of_loop imps x i = ok o) : o.val = imps.val ++ x.val.drop i.val := by
  rw [hdr_of_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len x
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as y, hy
    obtain ⟨_hb, rfl⟩ := vec_index_eq hy
    peel h as y1, hy1
    cases import_rec_dup_ok hy1
    peel h as imps1, hi1
    peel h as i2, hi2
    have ih := hdr_of_loop_eq imps1 x i2 h
    rw [usize_succ hi2, ConRon.Refine.vec_push_val hi1] at ih
    rw [ih, drop_cons_of_lt hlt']
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by x.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

theorem catchAt_ok {α : Type} {x : AM α} {lst lst1 : AState} {b : α} (hx : x.run lst = .ok (b, lst1)) :
    (Modular.AM.catchAt x).run lst = .ok (.ok b, lst1) := by
  have : x lst = .ok (b, lst1) := hx
  show (match x lst with
    | .ok (a, s') => Except.ok (Except.ok a, s')
    | .error e => .ok (.error e, lst)) = _
  rw [this]

section io

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier} {sp : frontend.olean.files.Roots}
  {cmp : Option (arena.handle.NIdx × arena.handle.NIdx)}

/-- **`hdr_of`'s accept is `hdrOf`.** -/
theorem hdr_of_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {m : arena.handle.NIdx} :
    AS pers (EqA absNode) st lst (hdr_of inst fsv pk pers st.store sp cmp m)
      (Modular.hdrOf fs (absPins pk) (absRoots sp) (absCmp cmp) (absNIdx m)) := by
  intro hrel hinv a s' h
  rw [hdr_of] at h
  peel h as ⟨r, ar1⟩, hr
  cases r with
  | Err e =>
    peel h as r1, -
    cases r1 with
    | Err e2 => cases Result.ok_injective h
    | Ok b =>
      dsimp only at h
      cases b with
      | false => cases Result.ok_injective h
      | true =>
        simp only [↓reduceIte] at h
        peel h as _s, -
        peel h as _v, -
        peel h as _v1, -
        peel h as _t, -
        peel h as _s1, -
        peel h as _v2, -
        peel h as _v3, -
        peel h as _ce, -
        cases Result.ok_injective h
  | Ok imps =>
    obtain ⟨b1, lst1, hx, hR, hrel1, hinv1⟩ := module_imports_refines (st := st) (lst := lst) (sp := sp)
      (m := m) hfs hrel hinv _ _ hr
    cases show b1 = absImports imps from hR
    peel h as x, hx1
    have ex := cmp_extra_eq hx1
    peel h as imps1, hi1
    have ei := hdr_of_loop_eq imps x _ hi1
    peel h as n, hn
    cases nidx_dup2_ok hn
    cases Result.ok_injective h
    refine ⟨(absNIdx m, absImports imps ++ Modular.cmpExtra (absCmp cmp) (absNIdx m)), lst1, ?_, ?_, hrel1, hinv1⟩
    · show ((Modular.AM.catchAt _) >>= _).run lst = _
      rw [am_bind_ok (catchAt_ok hx)]
      rfl
    · show _ = (absNIdx m, absImports imps1)
      rw [← ex]
      simp [absImports, ei]

theorem level_hdrs_loop_ok (hfs : FsRel inst fsv fs) (lvl : alloc.vec.Vec arena.handle.NIdx)
    (st : arena.monad.AState) (lst : AState)
    (rs : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (i : Std.Usize) {acc : List Node} (ho : rs.val.map absNode = acc) :
    AS pers (fun (o : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
        (ys : List Node) => o.val.map absNode = acc ++ ys) st lst
      (level_hdrs_loop inst fsv pk pers st.store sp cmp lvl rs i)
      (((lvl.val.drop i.val).map absNIdx).mapM (Modular.hdrOf fs (absPins pk) (absRoots sp) (absCmp cmp))) := by
  intro hrel hinv a s' h
  rw [level_hdrs_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len lvl
  · rw [ite_eq_left hlt] at h
    have hlt' := lt_len hlt
    peel h as n, hn
    obtain ⟨_hb, rfl⟩ := vec_index_eq hn
    peel h as ⟨r, ar1⟩, hq
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok r1 =>
      obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := hdr_of_refines hfs hrel hinv _ _ hq
      peel h as rs1, hrs1
      peel h as i2, hi2
      have ho' : rs1.val.map absNode = acc ++ [b] := by
        rw [ConRon.Refine.vec_push_val hrs1, List.map_append, ho, hR]; rfl
      obtain ⟨ys, lst2, hys, hF, hrel2, hinv2⟩ :=
        level_hdrs_loop_ok hfs lvl (withStore st ar1) lst1 rs1 i2 ho' hrel1 hinv1 a s' h
      rw [usize_succ hi2] at hys
      refine ⟨b :: ys, lst2, ?_, by simpa using hF, hrel2, hinv2⟩
      rw [drop_cons_of_lt hlt', List.map_cons, List.mapM_cons]
      rw [am_bind_ok hx, am_bind_ok hys]
      rfl
  · rw [ite_eq_right hlt] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨[], lst, rfl, by simpa using ho, hrel, hinv⟩
termination_by lvl.val.length - i.val
decreasing_by rw [usize_succ hi2]; omega

/-- **`level_hdrs`'s accept is the level's headers, read in order.** -/
theorem level_hdrs_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {lvl : alloc.vec.Vec arena.handle.NIdx} :
    AS pers (fun (o : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
        (ys : List Node) => o.val.map absNode = ys) st lst
      (level_hdrs inst fsv pk pers st.store sp cmp lvl)
      ((lvl.val.map absNIdx).mapM (Modular.hdrOf fs (absPins pk) (absRoots sp) (absCmp cmp))) := by
  intro hrel hinv a s' h
  rw [level_hdrs] at h
  have := level_hdrs_loop_ok hfs lvl st lst _ _ (acc := []) (by simp) hrel hinv a s' h
  simpa using this

theorem level_fuel_val {x : Std.U64} (h : LEVEL_FUEL = ok x) : x.val = ConLeche.Driver.Graph.levelFuel := by
  rw [LEVEL_FUEL] at h
  have := (ConRon.Refine.Nat.ushiftLeftI_val h).2
  rw [this]; decide

theorem closure_levels_loop_ok (hfs : FsRel inst fsv fs) (f : Nat) (st : arena.monad.AState) (lst : AState)
    (lvl : alloc.vec.Vec arena.handle.NIdx) (seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (out : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (fuel : Std.U64) (hf : fuel.val = f) {S : _root_.Std.HashSet NIdx} (hs : NSet seen S) :
    AS pers (fun o C => absC o = C) st lst
      (closure_levels_loop inst fsv pk pers st.store sp cmp lvl seen out fuel)
      (Modular.closureLevels fs (absPins pk) (absRoots sp) (absCmp cmp) f (lvl.val.map absNIdx) S (absC out)) := by
  intro hrel hinv a s' h
  rw [closure_levels_loop] at h
  by_cases hp : alloc.vec.Vec.len lvl > 0#usize
  swap
  · rw [ite_eq_right hp] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len lvl).val := hp
    have e : lvl.val = [] := by
      rw [vec_len_val] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    rw [e]
    exact ⟨_, lst, by rw [List.map_nil, Modular.closureLevels]; rfl, rfl, hrel, hinv⟩
  rw [ite_eq_left hp] at h
  have hp' : 0 < lvl.val.length := by
    have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len lvl).val := hp
    rw [vec_len_val] at this; simpa using this
  obtain ⟨x, xs, hl⟩ : ∃ x xs, lvl.val.map absNIdx = x :: xs := by
    cases hc : lvl.val with
    | nil => rw [hc] at hp'; simp at hp'
    | cons y ys => exact ⟨_, _, rfl⟩
  by_cases h0 : fuel = 0#u64
  · rw [ite_eq_left h0] at h
    peel h as _s, -
    peel h as _v, -
    peel h as _ce, -
    cases Result.ok_injective h
  rw [ite_eq_right h0] at h
  peel h as fuel1, hfuel1
  have hfv : fuel1.val = f - 1 := by rw [fuel_pred hfuel1, hf]
  have hfp : f ≠ 0 := by
    intro hz; apply h0; apply UScalar.eq_of_val_eq; rw [hf, hz]; rfl
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  peel h as ⟨r, ar1⟩, hq
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok rs =>
    obtain ⟨ys, lst1, hx, hR, hrel1, hinv1⟩ := level_hdrs_refines (cmp := cmp) hfs hrel hinv _ _ hq
    peel h as ⟨seen1, out1, next⟩, hexp
    obtain ⟨e1, e2, e3⟩ := expand_eq pk hs hexp
    have ih := closure_levels_loop_ok hfs f' (withStore st ar1) lst1 next seen1 out1 fuel1 (by rw [hfv]; rfl)
      e1 hrel1 hinv1 a s' h
    rw [hl, Modular.closureLevels]
    rw [← hl, am_bind_ok hx]
    simp only [← hR] at e2 e3 e1 ⊢
    have en : (absNs (alloc.vec.Vec.new arena.handle.NIdx)) = #[] := by simp
    rw [en] at e2 e3 e1 ih
    rw [← e2, ← e3]
    have et : (absNs next).toList = next.val.map absNIdx := by simp
    rw [et]
    exact ih
termination_by f
decreasing_by omega

/-- **`closure_levels`'s accept is `closureLevels`** at upstream's fuel. -/
theorem closure_levels_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {lvl : alloc.vec.Vec arena.handle.NIdx} {seen : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {out : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {S : _root_.Std.HashSet NIdx} (hs : NSet seen S) :
    AS pers (fun o C => absC o = C) st lst
      (closure_levels inst fsv pk pers st.store sp cmp lvl seen out)
      (Modular.closureLevels fs (absPins pk) (absRoots sp) (absCmp cmp) ConLeche.Driver.Graph.levelFuel
        (lvl.val.map absNIdx) S (absC out)) := by
  intro hrel hinv a s' h
  rw [closure_levels] at h
  peel h as fuel, hfuel
  exact closure_levels_loop_ok hfs _ st lst lvl seen out fuel (level_fuel_val hfuel) hs hrel hinv a s' h

/-- **`graph_of`'s accept is `graphOf`**: the closure, its graph checked. -/
theorem graph_of_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {roots : alloc.vec.Vec arena.handle.NIdx} :
    AS pers (fun c C => absC c = C) st lst
      (graph_of inst fsv pk pers st.store sp roots cmp)
      (Modular.graphOf fs (absPins pk) (absRoots sp) (roots.val.map absNIdx) (absCmp cmp)) := by
  intro hrel hinv a s' h
  rw [graph_of] at h
  peel h as ⟨lvl, seen⟩, hd
  obtain ⟨el, es⟩ := dedup_eq hd
  peel h as ⟨r, ar1⟩, hq
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok c =>
    obtain ⟨C, lst1, hx, hR, hrel1, hinv1⟩ := closure_levels_refines (cmp := cmp) hfs es hrel hinv _ _ hq
    dsimp only at h
    peel h as idx, hidx
    have eidx := index_of_eq hidx
    peel h as deps, hdeps
    obtain ⟨edeps, fdeps⟩ := deps_of_eq eidx hdeps
    peel h as ord, hord
    obtain ⟨eord, ford⟩ := kahn_eq fdeps hord
    peel h as cy, hcy
    have ecy := cycle_of_eq fdeps ford hcy
    cases cy with
    | some _ =>
      dsimp only at h
      peel h as _s, -
      peel h as _v, -
      peel h as _v1, -
      peel h as _t, -
      peel h as _ce, -
      cases Result.ok_injective h
    | none =>
      dsimp only at h
      peel h as i1, hi1
      have ei1 := cast_u64_val hi1
      peel h as v, hv
      have ev := ranks_of_eq ford hv
      peel h as o1, ho1
      have eo1 := verdict_eq eidx ho1
      cases o1 with
      | some _ =>
        dsimp only at h
        peel h as _ce, -
        cases Result.ok_injective h
      | none =>
        dsimp only at h
        cases Result.ok_injective h
        refine ⟨C, lst1, ?_, hR, hrel1, hinv1⟩
        subst hR
        rw [edeps] at ecy eord
        rw [eord] at ecy ev
        simp only [absRk] at eo1
        rw [ev, ei1] at eo1
        have esz : (alloc.vec.Vec.len a).val = (absC a).size := by simp
        rw [esz] at eo1
        have e0 : absC (alloc.vec.Vec.new (arena.handle.NIdx ×
            alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))) = #[] := by simp
        rw [e0] at hx
        simp only at el
        rw [el] at hx
        unfold Modular.graphOf
        generalize Modular.dedup (roots.val.map absNIdx) = dd at hx
        obtain ⟨L, T⟩ := dd
        dsimp only at hx ⊢
        rw [am_bind_ok hx]
        simp only [Option.map_none] at ecy eo1
        rw [← ecy]
        dsimp only
        rw [← eo1]
        rfl

end io

end ConRon.Refine2.Modular

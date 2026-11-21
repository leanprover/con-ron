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

end ConRon.Refine2.Modular

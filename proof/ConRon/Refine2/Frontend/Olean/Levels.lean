/-
# `ConRon.Refine2.Frontend.Olean.Levels` — `olean/levels.rs`: the header fixpoint

**Task #166, Theorem 2.**  The flags, the fixpoint's worklist (`levels_go`, which reads
headers, so it claims its accept, `AS`), `header_fixpoint`, the `ModSet` operations against
upstream's on `ByteArray`, and the public-import closures, against the twin's.

**The relations.**  `LoadFlags` is upstream's (`absLoadFlags`); a `HashMap2` keyed by name
handles is a `Std.HashMap NIdx` (`NMapRel`), the `open` table an `NSet`, a `Vec<u8>` a
`ByteArray` (`absChunk`); the worklist is a `StackRel` of `absLvWork`.
-/
import ConRon.Refine2.Frontend.Olean.ClosureRead
import ConRon.Arena.Frontend.Olean.Levels

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.levels

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine2.Frontend (absChunk absByte)
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Refine2.Lockstep (LSP)

/-! ## The abstractions -/

/-- `levels::LoadFlags`, as upstream's. -/
@[reducible] def absLoadFlags (l : frontend.olean.levels.LoadFlags) : ConLeche.Frontend.Olean.LoadFlags :=
  ⟨l.import_all, l.is_exported⟩

/-- A step of the worklist, as the twin's. -/
def absLvWork : frontend.olean.levels.LvWork → Arena.Frontend.Olean.LvWork
  | .Imp pf i => .imp (absLoadFlags pf) (absImportF absNIdx i)
  | .Done m fl => .done (absNIdx m) (absLoadFlags fl)

/-- The hash of name handles. -/
abbrev hN := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
/-- The equality of name handles. -/
abbrev eN := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2

/-- **A `HashMap2` keyed by name handles**, as a `Std.HashMap` of what they stand for. -/
structure NMapRel {V V' : Type} (A : V → V') (m : ron.hashmap2.HashMap2 arena.handle.NIdx V)
    (s : _root_.Std.HashMap NIdx V') : Prop where
  inv : Inv hN m
  get : ∀ k, (toFun m k).map A = s[absNIdx k]?

/-- **The fixpoint's state**, field by field. -/
structure LvStateRel (st : frontend.olean.levels.LvState) (st' : Arena.Frontend.Olean.LvState) :
    Prop where
  flags : NMapRel absLoadFlags st.flags st'.flags
  open_ : NSet st.«open» st'.open_
  order : OutA st.order st'.order
  imports : NMapRel absImports st.imports st'.imports

/-- **`levels::HeaderLoads` against the twin's `HeaderLoads`**. -/
structure HeaderLoadsRel (ld : frontend.olean.levels.HeaderLoads)
    (ld' : Arena.Frontend.Olean.HeaderLoads) : Prop where
  order : OutA ld.order ld'.order
  flags : ld.flags.val.map absLoadFlags = ld'.flags.toList
  imports : ld.imports.val.map absImports = ld'.imports.toList
  index : NMapRel (fun x : Std.U64 => x.val) ld.index ld'.index

/-! ## `NMapRel` -/

section NMapRel
variable {V V' : Type} {A : V → V'} {m : ron.hashmap2.HashMap2 arena.handle.NIdx V}
  {s : _root_.Std.HashMap NIdx V'}

theorem NMapRel.get_eq (h : NMapRel A m s) {k : arena.handle.NIdx} {o : Option V}
    (hg : ron.hashmap2.HashMap2.get hN eN m k = ok o) : o.map A = s[absNIdx k]? := by
  rw [ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 h.inv (fun _ _ => trivial) trivial hg]
  exact h.get k

theorem NMapRel.contains_eq (h : NMapRel A m s) {k : arena.handle.NIdx} {b : Bool}
    (hg : ron.hashmap2.HashMap2.contains_key hN eN m k = ok b) : b = s.contains (absNIdx k) := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 h.inv (fun _ _ => trivial) trivial hg,
    _root_.Std.HashMap.contains_eq_isSome_getElem?, ← h.get k]
  cases toFun m k <;> rfl

theorem NMapRel.insert (h : NMapRel A m s) {k : arena.handle.NIdx} {v : V} {old} {m'}
    (hi : ron.hashmap2.HashMap2.insert hN eN m k v = ok (old, m')) :
    NMapRel A m' (s.insert (absNIdx k) (A v)) := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (absNIdx k == absNIdx k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem NMapRel.remove (h : NMapRel A m s) {k : arena.handle.NIdx} {old} {m'}
    (hi : ron.hashmap2.HashMap2.remove hN eN m k = ok (old, m')) :
    old.map A = s[absNIdx k]? ∧ NMapRel A m' (s.erase (absNIdx k)) := by
  obtain ⟨hinv, hold, hupd, -⟩ := ConRon.Refine.HashMap2.remove_refines_gen nidx_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨by rw [hold]; exact h.get k, hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_erase]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (absNIdx k == absNIdx k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem NMapRel.new (hn : ron.hashmap2.HashMap2.new arena.handle.NIdx V = ok m) :
    NMapRel A m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hN) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

theorem NMapRel.with_capacity {c : Std.Usize}
    (hn : ron.hashmap2.HashMap2.with_capacity arena.handle.NIdx V c = ok m) : NMapRel A m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines (HashableInst := hN) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

end NMapRel

/-- `remove` is `erase`, on a set. -/
theorem NSet.remove {m m' : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {s : _root_.Std.HashSet NIdx}
    {k : arena.handle.NIdx} {old} (hs : NSet m s)
    (hi : ron.hashmap2.HashMap2.remove hN eN m k = ok (old, m')) : NSet m' (s.erase (absNIdx k)) := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.remove_refines_gen nidx_eq2
    hs.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashSet.contains_erase]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (absNIdx k == absNIdx k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using hs.mem k1

/-! ## The flags and the steps -/

/-- **`load_flags_dup` is the identity.** -/
theorem load_flags_dup_eq {l o : frontend.olean.levels.LoadFlags} (h : load_flags_dup l = ok o) :
    o = l := by
  rw [load_flags_dup] at h
  exact (Result.ok_injective h).symm

/-- **`load_flags_beq` is the derived `BEq`.** -/
theorem load_flags_beq_eq {a b : frontend.olean.levels.LoadFlags} {o : Bool}
    (h : load_flags_beq a b = ok o) : o = (absLoadFlags a == absLoadFlags b) := by
  rw [load_flags_beq] at h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  by_cases e : a1 = b1
  · rw [ite_eq_left e] at h
    cases Result.ok_injective h
    subst e
    cases a1 <;> cases a2 <;> cases b2 <;> decide
  · rw [ite_eq_right e] at h
    cases Result.ok_injective h
    cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> simp_all <;> decide

/-- **`load_flags_level` is `LoadFlags.level`.** -/
theorem load_flags_level_eq {l : frontend.olean.levels.LoadFlags} {o}
    (h : load_flags_level l = ok o) : absLevel o = (absLoadFlags l).level := by
  rw [load_flags_level] at h
  unfold ConLeche.Frontend.Olean.LoadFlags.level
  by_cases e : l.import_all = true
  · rw [ite_eq_left e] at h
    cases Result.ok_injective h
    simp [e, absLevel]
  · rw [ite_eq_right e] at h
    cases Result.ok_injective h
    simp [e, absLevel]

/-- **`import_rec_dup` is the identity.** -/
theorem import_rec_dup_eq {i o : frontend.olean.spec.ImportF arena.handle.NIdx}
    (h : import_rec_dup i = ok o) : o = i := by
  rw [import_rec_dup] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  exact (Result.ok_injective h).symm

/-- **`lv_work_dup` is the identity.** -/
theorem lv_work_dup_eq {w o : frontend.olean.levels.LvWork} (h : lv_work_dup w = ok o) : o = w := by
  cases w with
  | Imp pf i =>
    rw [lv_work_dup.eq_def] at h
    dsimp only at h
    peel h as lf, hlf
    cases load_flags_dup_eq hlf
    peel h as j, hj
    cases import_rec_dup_eq hj
    exact (Result.ok_injective h).symm
  | Done m fl =>
    rw [lv_work_dup.eq_def] at h
    dsimp only at h
    peel h as n, hn
    cases nidx_dup2_ok hn
    peel h as lf, hlf
    cases load_flags_dup_eq hlf
    exact (Result.ok_injective h).symm

end ConRon.Refine2.Frontend.Olean

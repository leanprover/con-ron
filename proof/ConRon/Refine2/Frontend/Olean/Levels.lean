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

/-! ## The worklist -/

/-- **`lv_push`**: the step on top. -/
theorem lv_push_eq {stack : alloc.vec.Vec frontend.olean.levels.LvWork} {sp : Std.Usize}
    {l : List Arena.Frontend.Olean.LvWork} {x i st1} (h : StackRel absLvWork stack sp l)
    (hr : lv_push stack sp x = ok (i, st1)) : StackRel absLvWork st1 i (absLvWork x :: l) := by
  rw [lv_push] at hr
  peel hr as t, ht
  peel hr as i1, hi1
  cases Result.ok_injective hr
  exact h.push ht hi1

theorem lv_push_imports_loop_eq (fl : frontend.olean.levels.LoadFlags)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    (stack : alloc.vec.Vec frontend.olean.levels.LvWork) (s i : Std.Usize)
    {l : List Arena.Frontend.Olean.LvWork} (hl : StackRel absLvWork stack s l) {o}
    (h : lv_push_imports_loop stack fl imps s i = ok o) :
    StackRel absLvWork o.2 o.1 ((imps.val.take i.val).map (fun x => absLvWork (.Imp fl x)) ++ l) := by
  rw [lv_push_imports_loop] at h
  by_cases hp : i > 0#usize
  · rw [ite_eq_left hp] at h
    peel h as i1, hi1
    have hv := ConRon.Refine.HashMap.uscalar_sub_eq hi1
    have l1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [l1] at hv
    have hp' : (0#usize : Std.Usize).val < i.val := hp
    have l0 : (0#usize : Std.Usize).val = 0 := by decide
    rw [l0] at hp'
    have e : i.val = i1.val + 1 := by omega
    peel h as lf, hlf
    cases load_flags_dup_eq hlf
    peel h as x, hx
    obtain ⟨hb, rfl⟩ := vec_index_eq hx
    peel h as y, hy
    cases import_rec_dup_eq hy
    peel h as q, hq
    obtain ⟨s1, st1⟩ := q
    have := lv_push_imports_loop_eq fl imps st1 s1 i1 (lv_push_eq hl hq) h
    rw [e, List.take_succ_eq_append_getElem hb, List.map_append, List.append_assoc]
    exact this
  · rw [ite_eq_right hp] at h
    cases Result.ok_injective h
    have : ¬ (0#usize : Std.Usize).val < i.val := hp
    have e : i.val = 0 := by simpa using this
    rw [e]
    simpa using hl
termination_by i.val
decreasing_by omega

theorem ofImports_abs (fl : frontend.olean.levels.LoadFlags)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    imps.val.map (fun x => absLvWork (.Imp fl x)) =
      Arena.Frontend.Olean.LvWork.ofImports (absLoadFlags fl) (absImports imps) := by
  simp [Arena.Frontend.Olean.LvWork.ofImports, absLvWork, Function.comp_def]

/-- **`lv_push_imports` is `LvWork.ofImports fl imps ++ rest`.** -/
theorem lv_push_imports_eq {stack : alloc.vec.Vec frontend.olean.levels.LvWork} {sp : Std.Usize}
    {fl : frontend.olean.levels.LoadFlags}
    {imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {l : List Arena.Frontend.Olean.LvWork} (hl : StackRel absLvWork stack sp l) {o}
    (h : lv_push_imports stack sp fl imps = ok o) :
    StackRel absLvWork o.2 o.1
      (Arena.Frontend.Olean.LvWork.ofImports (absLoadFlags fl) (absImports imps) ++ l) := by
  rw [lv_push_imports] at h
  have := lv_push_imports_loop_eq fl imps stack sp _ hl h
  rwa [vec_len_val, List.take_length, ofImports_abs] at this

/-- **`levels_again`**: a met module's imports, at the joined flags, on top. -/
theorem levels_again_eq {stack : alloc.vec.Vec frontend.olean.levels.LvWork} {sp : Std.Usize}
    {imports : ron.hashmap2.HashMap2 arena.handle.NIdx
      (alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {im : _root_.Std.HashMap NIdx (_root_.Array (ConLeche.Frontend.Olean.ImportF NIdx))}
    (hi : NMapRel absImports imports im) {fl : frontend.olean.levels.LoadFlags} {m : arena.handle.NIdx}
    {l : List Arena.Frontend.Olean.LvWork} (hl : StackRel absLvWork stack sp l) {o}
    (h : levels_again stack sp imports fl m = ok o) :
    StackRel absLvWork o.2 o.1 (match im[absNIdx m]? with
      | some is => Arena.Frontend.Olean.LvWork.ofImports (absLoadFlags fl) is ++ l
      | none => l) := by
  rw [levels_again] at h
  peel h as r, hr
  have er := hi.get_eq hr
  cases r with
  | none =>
    rw [← er]
    cases Result.ok_injective h
    exact hl
  | some is =>
    rw [← er]
    exact lv_push_imports_eq hl h

/-- The join of a placed module's flags with new ones, where they grow. -/
def joinF (old? : Option ConLeche.Frontend.Olean.LoadFlags) (fl : ConLeche.Frontend.Olean.LoadFlags) :
    Option ConLeche.Frontend.Olean.LoadFlags :=
  match old? with
  | none => none
  | some old =>
    let fl' : ConLeche.Frontend.Olean.LoadFlags :=
      { importAll := fl.importAll || old.importAll, isExported := fl.isExported || old.isExported }
    if fl' == old then none else some fl'

/-- **`levels_join` is `joinF`.** -/
theorem levels_join_eq {flags : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.levels.LoadFlags}
    {F : _root_.Std.HashMap NIdx ConLeche.Frontend.Olean.LoadFlags} (hF : NMapRel absLoadFlags flags F)
    {fl : frontend.olean.levels.LoadFlags} {m : arena.handle.NIdx} {o}
    (h : levels_join flags fl m = ok o) :
    o.map absLoadFlags = joinF F[absNIdx m]? (absLoadFlags fl) := by
  rw [levels_join] at h
  peel h as r, hr
  have er := hF.get_eq hr
  rw [← er]
  cases r with
  | none => cases Result.ok_injective h; rfl
  | some old =>
    dsimp only at h
    peel h as q1, hq1
    obtain ⟨old1, b⟩ := q1
    have e1 : old1 = old ∧ b = (fl.import_all || old.import_all) := by
      clear h; revert hq1
      cases fl.import_all <;> intro hq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hq) <;> simp
    obtain ⟨rfl, rfl⟩ := e1
    peel h as q2, hq2
    obtain ⟨old2, b1⟩ := q2
    have e2 : old2 = old1 ∧ b1 = (fl.is_exported || old1.is_exported) := by
      clear h; revert hq2
      cases fl.is_exported <;> intro hq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hq) <;> simp
    obtain ⟨rfl, rfl⟩ := e2
    peel h as b2, hb2
    have eb := load_flags_beq_eq hb2
    simp only [Option.map_some, joinF]
    by_cases cb : b2 = true
    · rw [ite_eq_left cb] at h
      cases Result.ok_injective h
      rw [← eb, cb]; rfl
    · rw [ite_eq_right cb] at h
      cases Result.ok_injective h
      have : b2 = false := by simpa using cb
      rw [← eb, this]; rfl

/-! ## The twin's worklist -/

section twin
open Arena.Frontend.Olean (levelsGo levelsJoin)
variable {fs : Arena.Frontend.Olean.OleanFs} {pk : Arena.Frontend.Olean.OleanPins} {sp : ConLeche.Frontend.Olean.Roots}
  {gp : Bool} {f : Nat} {rest : List Arena.Frontend.Olean.LvWork} {st : Arena.Frontend.Olean.LvState}

theorem levelsJoin_eq {fl : ConLeche.Frontend.Olean.LoadFlags} {m : NIdx} :
    levelsJoin st fl m rest = match joinF st.flags[m]? fl with
      | none => (rest, st)
      | some fl' => (match st.imports[m]? with
          | some is => Arena.Frontend.Olean.LvWork.ofImports fl' is ++ rest
          | none => rest, { st with flags := st.flags.insert m fl' }) := by
  unfold levelsJoin joinF
  cases st.flags[m]? with
  | none => rfl
  | some old =>
    dsimp only
    split
    · rfl
    · cases st.imports[m]? <;> rfl

theorem lgo_nil {s : Arena.Frontend.Olean.LvState} : levelsGo fs pk sp gp f [] s = pure s := by
  cases f <;> rw [levelsGo]

theorem lgo_done {m fl} :
    levelsGo fs pk sp gp (f + 1) (.done m fl :: rest) st =
      levelsGo fs pk sp gp f rest
        { st with flags := st.flags.insert m fl, open_ := st.open_.erase m, order := st.order.push m } := by
  rw [levelsGo]

theorem lgo_skip {pf i} (hg : (i.isExported || pf.importAll) = false) :
    levelsGo fs pk sp gp (f + 1) (.imp pf i :: rest) st = levelsGo fs pk sp gp f rest st := by
  rw [levelsGo, hg]; rfl

theorem lgo_join {pf i fl} (hg : (i.isExported || pf.importAll) = true)
    (hfl : fl = ⟨gp || (pf.importAll && i.importAll), pf.isExported && i.isExported⟩)
    (hc : st.flags.contains i.module = true) :
    levelsGo fs pk sp gp (f + 1) (.imp pf i :: rest) st =
      levelsGo fs pk sp gp f (levelsJoin st fl i.module rest).1 (levelsJoin st fl i.module rest).2 := by
  subst hfl
  rw [levelsGo, hg]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc]

theorem lgo_new {pf i fl} {lst lst1 : AState} {is}
    (hg : (i.isExported || pf.importAll) = true)
    (hfl : fl = ⟨gp || (pf.importAll && i.importAll), pf.isExported && i.isExported⟩)
    (hc : st.flags.contains i.module = false)
    (ho : st.open_.contains i.module = false)
    (hx : (Arena.Frontend.Olean.moduleImports fs pk sp i.module).run lst = .ok (is, lst1)) :
    (levelsGo fs pk sp gp (f + 1) (.imp pf i :: rest) st).run lst =
      (levelsGo fs pk sp gp f (Arena.Frontend.Olean.LvWork.ofImports fl is ++ .done i.module fl :: rest)
        { st with open_ := st.open_.insert i.module, imports := st.imports.insert i.module is }).run lst1 := by
  subst hfl
  rw [levelsGo, hg]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc, ho]
  exact am_bind_ok hx

end twin

/-! ## `levels_go` -/

section walk

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
  {sp_dirs : frontend.olean.files.Roots}

/-- **`levels_go`'s loop against `levelsGo`.** -/
theorem levels_go_loop_ok (hfs : FsRel inst fsv fs) (gp : Bool)
    (f : Nat) (st : arena.monad.AState) (lst : AState) (stack : alloc.vec.Vec frontend.olean.levels.LvWork)
    (sp : Std.Usize) (fuel : Std.U64) (s : frontend.olean.levels.LvState)
    (l : List Arena.Frontend.Olean.LvWork) (s' : Arena.Frontend.Olean.LvState)
    (hf : fuel.val = f) (hl : StackRel absLvWork stack sp l) (hs : LvStateRel s s') :
    AS pers LvStateRel st lst (levels_go_loop inst fsv pk pers st.store sp_dirs gp stack sp s fuel)
      (Arena.Frontend.Olean.levelsGo fs (absPins pk) (absRoots sp_dirs) gp f l s') := by
  intro hrel hinv a s2 h
  rw [levels_go_loop] at h
  by_cases hsp : sp > 0#usize
  swap
  · rw [ite_eq_right hsp] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    have hnil := hl.nil_of_zero hsp
    subst hnil
    rw [lgo_nil]
    exact ⟨s', lst, rfl, hs, hrel, hinv⟩
  rw [ite_eq_left hsp] at h
  by_cases h0 : fuel = 0#u64
  · rw [ite_eq_left h0] at h
    peel h as r0, hr0
    rw [levels_out_of_fuel] at hr0
    peel hr0 as s0, -
    peel hr0 as v0, -
    peel hr0 as ce, -
    cases Result.ok_injective hr0
    cases (Prod.mk.inj (Result.ok_injective h)).1
  rw [ite_eq_right h0] at h
  peel h as fuel1, hfuel1
  peel h as sp1, hsp1
  peel h as lw, hlw
  peel h as lw1, hlw1
  cases lv_work_dup_eq hlw1
  obtain ⟨hi, l', rfl, hl'⟩ := hl.pop hsp hsp1
  obtain ⟨hi', he⟩ := vec_index_eq hlw
  rw [← he]
  have hfv : fuel1.val = f - 1 := by
    rw [ConRon.Refine.HashMap.uscalar_sub_eq hfuel1, hf]; rfl
  have hfp : f ≠ 0 := by
    intro hz
    apply h0
    apply UScalar.eq_of_val_eq
    rw [hf, hz]; rfl
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hfv' : fuel1.val = f' := by rw [hfv]; rfl
  cases lw with
  | Done m fl =>
    dsimp only at h
    peel h as n, hn
    cases nidx_dup2_ok hn
    peel h as p, hp
    obtain ⟨_, hm⟩ := p
    peel h as p2, hp2
    obtain ⟨_, hm1⟩ := p2
    peel h as v, hv
    have ho' : OutA v (s'.order.push (absNIdx m)) := by
      show v.val.map absNIdx = _
      rw [ConRon.Refine.vec_push_val hv, List.map_append, hs.order]
      simp
    rw [absLvWork, lgo_done]
    exact levels_go_loop_ok hfs gp f' st lst stack sp1 fuel1
      { flags := hm, «open» := hm1, order := v, imports := s.imports } l'
      { s' with flags := s'.flags.insert (absNIdx m) (absLoadFlags fl), open_ := s'.open_.erase (absNIdx m),
                order := s'.order.push (absNIdx m) } hfv' hl'
      ⟨hs.flags.insert hp, NSet.remove hs.open_ hp2, ho', hs.imports⟩ hrel hinv a s2 h
  | Imp pf i =>
    dsimp only at h
    by_cases hskip : (i.is_exported || pf.import_all) = false
    · have e1 : i.is_exported = false := by simp_all
      have e2 : pf.import_all = false := by simp_all
      simp only [e1, e2, Bool.false_eq_true, ↓reduceIte] at h
      rw [absLvWork, lgo_skip (by simpa [absImportF] using hskip)]
      exact levels_go_loop_ok hfs gp f' st lst stack sp1 fuel1 s l' s' hfv' hl' hs hrel hinv a s2 h
    have hg : ((absImportF absNIdx i).isExported || (absLoadFlags pf).importAll) = true := by
      cases h1 : i.is_exported <;> cases h2 : pf.import_all <;> simp_all [absImportF]
    by_cases hie : i.is_exported = true
    on_goal 1 =>
      rw [ite_eq_left hie] at h
      peel h as q, hq
      obtain ⟨pf1, b⟩ := q
      have eq : pf1 = pf ∧ b = (gp || (pf.import_all && i.import_all)) := by
        clear h; revert hq
        cases gp <;> cases pf.import_all <;> intro hq <;> simp at hq <;>
          obtain ⟨rfl, rfl⟩ := hq <;> simp
      obtain ⟨hpf, eb⟩ := eq
      rw [hpf] at h
      peel h as b1, hb1
      have eb1 : b1 = (pf.is_exported && i.is_exported) := by
        clear h; revert hb1
        cases pf.is_exported <;> intro hq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;>
          cases Result.ok_injective hq <;> simp
    on_goal 2 =>
      rw [ite_eq_right hie] at h
      have hpa : pf.import_all = true := by simp_all
      rw [ite_eq_left hpa] at h
      peel h as b, hb
      peel h as b1, hb1
      have eb : b = (gp || (pf.import_all && i.import_all)) := by
        clear h; revert hb
        cases gp <;> intro hq <;> simp only [Bool.false_eq_true, ↓reduceIte, hpa] at hq <;>
          cases Result.ok_injective hq <;> simp [hpa]
      have eb1 : b1 = (pf.is_exported && i.is_exported) := by
        clear h; revert hb1
        cases pf.is_exported <;> intro hq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;>
          cases Result.ok_injective hq <;> simp
    all_goals
      have hfl : absLoadFlags { import_all := b, is_exported := b1 } =
          ⟨gp || ((absLoadFlags pf).importAll && (absImportF absNIdx i).importAll),
            (absLoadFlags pf).isExported && (absImportF absNIdx i).isExported⟩ := by
        subst eb eb1; rfl
      peel h as b2, hb2
      have eb2 := hs.flags.contains_eq hb2
      by_cases cb : b2 = true
      · rw [ite_eq_left cb] at h
        peel h as o, ho
        have eo := levels_join_eq hs.flags ho
        have hc : s'.flags.contains (absNIdx i.module) = true := by rw [← eb2]; exact cb
        rw [absLvWork, lgo_join hg hfl hc, levelsJoin_eq]
        dsimp only [absImportF]
        rw [← eo]
        cases o with
        | none =>
          dsimp only at h
          exact levels_go_loop_ok hfs gp f' st lst stack sp1 fuel1 s l' s' hfv' hl' hs hrel hinv a s2 h
        | some fl2 =>
          dsimp only at h
          peel h as q1, hq1
          obtain ⟨sp2, stack1⟩ := q1
          peel h as q2, hq2
          obtain ⟨_, hm⟩ := q2
          have hS := levels_again_eq hs.imports hl' hq1
          exact levels_go_loop_ok hfs gp f' st lst stack1 sp2 fuel1 { s with flags := hm } _
            { s' with flags := s'.flags.insert (absNIdx i.module) (absLoadFlags fl2) } hfv' hS
            ⟨hs.flags.insert hq2, hs.open_, hs.order, hs.imports⟩ hrel hinv a s2 h
      · rw [ite_eq_right cb] at h
        have hc : s'.flags.contains (absNIdx i.module) = false := by
          rw [← eb2]; simpa using cb
        peel h as b3, hb3
        have eb3 := SetRel.contains_key nidx_eq2 hs.open_ hb3
        by_cases cb3 : b3 = true
        · rw [ite_eq_left cb3] at h
          peel h as ce, -
          cases (Prod.mk.inj (Result.ok_injective h)).1
        rw [ite_eq_right cb3] at h
        have ho : s'.open_.contains (absNIdx i.module) = false := by
          rw [← eb3]; simpa using cb3
        peel h as p, hp
        obtain ⟨r, ar1⟩ := p
        cases r with
        | Err x =>
          cases (Prod.mk.inj (Result.ok_injective h)).1
        | Ok imps =>
          obtain ⟨b4, lst1, hx, hR, hrel1, hinv1⟩ := module_imports_refines (st := st) (lst := lst)
            (sp := sp_dirs) hfs hrel hinv _ _ hp
          cases show b4 = absImports imps from hR
          peel h as n, hn
          cases nidx_dup2_ok hn
          peel h as lf, hlf
          cases load_flags_dup_eq hlf
          peel h as q1, hq1
          obtain ⟨sp2, stack1⟩ := q1
          peel h as q2, hq2
          obtain ⟨sp3, stack2⟩ := q2
          peel h as q3, hq3
          obtain ⟨_, hm⟩ := q3
          peel h as q4, hq4
          obtain ⟨_, hm1⟩ := q4
          have hS := lv_push_imports_eq (lv_push_eq hl' hq1) hq2
          rw [absLvWork, lgo_new hg hfl hc ho hx]
          exact levels_go_loop_ok hfs gp f' (withStore st ar1) lst1 stack2 sp3 fuel1
            { s with «open» := hm, imports := hm1 } _
            { s' with open_ := s'.open_.insert (absNIdx i.module),
                      imports := s'.imports.insert (absNIdx i.module) (absImports imps) } hfv' hS
            ⟨hs.flags, SetRel.insert nidx_eq2 absNIdx_inj hs.open_ hq3, hs.order, hs.imports.insert hq4⟩
            hrel1 hinv1 a s2 h
termination_by f
decreasing_by all_goals omega

/-- **`levels_go`'s accept is `levelsGo`**, at the closure's fuel. -/
theorem levels_go_refines (hfs : FsRel inst fsv fs) (gp : Bool) {st : arena.monad.AState} {lst : AState}
    {stack : alloc.vec.Vec frontend.olean.levels.LvWork} {top : Std.Usize}
    {l : List Arena.Frontend.Olean.LvWork} {s : frontend.olean.levels.LvState}
    {s' : Arena.Frontend.Olean.LvState} (hl : StackRel absLvWork stack top l) (hs : LvStateRel s s') :
    AS pers LvStateRel st lst (levels_go inst fsv pk pers st.store sp_dirs gp stack top s)
      (Arena.Frontend.Olean.levelsGo fs (absPins pk) (absRoots sp_dirs) gp
        ConLeche.Frontend.Olean.closureFuel l s') := by
  intro hrel hinv a s2 h
  rw [levels_go] at h
  peel h as fuel, hfuel
  exact levels_go_loop_ok hfs gp _ st lst stack top fuel s l s' (closure_fuel_val hfuel) hl hs
    hrel hinv a s2 h

end walk

/-! ## `header_fixpoint` -/

/-- `lv_state_empty` is the empty state. -/
theorem lv_state_empty_rel {o} (h : lv_state_empty = ok o) : LvStateRel o {} := by
  rw [lv_state_empty] at h
  peel h as h1, hh1
  peel h as h2, hh2
  peel h as h3, hh3
  cases Result.ok_injective h
  exact ⟨NMapRel.new hh1, nset_empty hh2, by simp [OutA, alloc.vec.Vec.new], NMapRel.new hh3⟩

/-- **`flags_at` is `(flags[m]?).getD default`.** -/
theorem flags_at_eq {flags : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.levels.LoadFlags}
    {F : _root_.Std.HashMap NIdx ConLeche.Frontend.Olean.LoadFlags} (hF : NMapRel absLoadFlags flags F)
    {m : arena.handle.NIdx} {o} (h : flags_at flags m = ok o) :
    absLoadFlags o = (F[absNIdx m]?).getD default := by
  rw [flags_at] at h
  peel h as r, hr
  rw [← hF.get_eq hr]
  cases r with
  | none => cases Result.ok_injective h; rfl
  | some fl =>
    dsimp only at h
    cases load_flags_dup_eq h
    rfl

/-- **`imports_out` is `(imports[m]?).getD #[]`**, the entry erased. -/
theorem imports_out_eq {im : ron.hashmap2.HashMap2 arena.handle.NIdx
      (alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    {I : _root_.Std.HashMap NIdx (_root_.Array (ConLeche.Frontend.Olean.ImportF NIdx))}
    (hI : NMapRel absImports im I) {m : arena.handle.NIdx} {v im'}
    (h : imports_out im m = ok (v, im')) :
    absImports v = (I[absNIdx m]?).getD #[] ∧ NMapRel absImports im' (I.erase (absNIdx m)) := by
  rw [imports_out] at h
  peel h as q, hq
  obtain ⟨r, im1⟩ := q
  obtain ⟨e, hrel⟩ := hI.remove hq
  rw [← e]
  cases r with
  | none =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨by simp [absImports, alloc.vec.Vec.new], hrel⟩
  | some is =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨rfl, hrel⟩

theorem header_loads_of_loop_eq
    (hm : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.levels.LoadFlags)
    (v : alloc.vec.Vec arena.handle.NIdx) (n : Std.Usize) (hn : n.val = v.val.length)
    {F : _root_.Std.HashMap NIdx ConLeche.Frontend.Olean.LoadFlags} (hF : NMapRel absLoadFlags hm F)
    (i : Std.Usize)
    (hm1 : ron.hashmap2.HashMap2 arena.handle.NIdx
      (alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (flags : alloc.vec.Vec frontend.olean.levels.LoadFlags)
    (imports : alloc.vec.Vec (alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)))
    (index : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64)
    {I : _root_.Std.HashMap NIdx (_root_.Array (ConLeche.Frontend.Olean.ImportF NIdx))}
    {fl : _root_.Array ConLeche.Frontend.Olean.LoadFlags}
    {is : _root_.Array (_root_.Array (ConLeche.Frontend.Olean.ImportF NIdx))}
    {ix : _root_.Std.HashMap NIdx Nat}
    (hI : NMapRel absImports hm1 I) (hfl : flags.val.map absLoadFlags = fl.toList)
    (his : imports.val.map absImports = is.toList) (hix : NMapRel (fun x : Std.U64 => x.val) index ix)
    {o} (h : header_loads_of_loop hm v hm1 n flags imports index i = ok o) :
    o.1.val.map absLoadFlags =
        (Arena.Frontend.Olean.HeaderLoads.ofStateGo F ((v.val.drop i.val).map absNIdx) i.val I fl is ix).1.toList ∧
      o.2.1.val.map absImports =
        (Arena.Frontend.Olean.HeaderLoads.ofStateGo F ((v.val.drop i.val).map absNIdx) i.val I fl is ix).2.1.toList ∧
      NMapRel (fun x : Std.U64 => x.val) o.2.2
        (Arena.Frontend.Olean.HeaderLoads.ofStateGo F ((v.val.drop i.val).map absNIdx) i.val I fl is ix).2.2 := by
  rw [header_loads_of_loop] at h
  by_cases hlt : i < n
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val < v.val.length := by have : i.val < n.val := hlt; omega
    peel h as x, hx
    obtain ⟨hb, rfl⟩ := vec_index_eq hx
    peel h as m, hm'
    cases nidx_dup2_ok hm'
    peel h as lf, hlf
    have elf := flags_at_eq hF hlf
    peel h as flags1, hflags1
    peel h as q, hq
    obtain ⟨v1, hm2⟩ := q
    obtain ⟨ev1, hI2⟩ := imports_out_eq hI hq
    peel h as imports1, himports1
    peel h as i1, hi1
    have hi1v : i1.val = i.val := by
      simp only [lift, Result.ok.injEq] at hi1
      subst hi1
      rw [usize_cast_u64_val']
    peel h as q2, hq2
    obtain ⟨_, index1⟩ := q2
    peel h as i2, hi2
    have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
    have ih := header_loads_of_loop_eq hm v n hn hF i2 hm2 flags1 imports1 index1 hI2
      (fl := fl.push ((F[absNIdx v.val[i.val]]?).getD default))
      (is := is.push ((I[absNIdx v.val[i.val]]?).getD #[]))
      (ix := ix.insert (absNIdx v.val[i.val]) i.val)
      (by rw [ConRon.Refine.vec_push_val hflags1, List.map_append, hfl, List.map_singleton, elf]; simp)
      (by rw [ConRon.Refine.vec_push_val himports1, List.map_append, his, List.map_singleton, ev1]; simp)
      (by have := hix.insert hq2; rwa [hi1v] at this) h
    rw [hi2v] at ih
    rw [List.drop_eq_getElem_cons hlt', List.map_cons, Arena.Frontend.Olean.HeaderLoads.ofStateGo]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : v.val.length ≤ i.val := by have : ¬ i.val < n.val := hlt; omega
    rw [List.drop_of_length_le hle, List.map_nil, Arena.Frontend.Olean.HeaderLoads.ofStateGo]
    exact ⟨hfl, his, hix⟩
termination_by v.val.length - i.val
decreasing_by
  have : i.val < n.val := hlt
  omega

/-- **`header_loads_of` is `HeaderLoads.ofState`.** -/
theorem header_loads_of_eq {st : frontend.olean.levels.LvState} {st' : Arena.Frontend.Olean.LvState}
    (hs : LvStateRel st st') {o} (h : header_loads_of st = ok o) :
    HeaderLoadsRel o (Arena.Frontend.Olean.HeaderLoads.ofState st') := by
  rw [header_loads_of] at h
  peel h as index, hindex
  peel h as q, hq
  obtain ⟨flags1, imports1, index1⟩ := q
  cases Result.ok_injective h
  have := header_loads_of_loop_eq st.flags st.order _ (vec_len_val _) hs.flags _ st.imports _ _ index
    hs.imports (fl := #[]) (is := #[]) (ix := {}) (by simp [alloc.vec.Vec.with_capacity])
    (by simp [alloc.vec.Vec.with_capacity]) (NMapRel.with_capacity hindex) hq
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero, hs.order] at this
  obtain ⟨e1, e2, e3⟩ := this
  exact ⟨hs.order, e1, e2, e3⟩

section walk

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
  {sp_dirs : frontend.olean.files.Roots}

/-- **`header_fixpoint`'s accept is `headerFixpoint`.** -/
theorem header_fixpoint_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {is_module : Bool} {imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)} :
    AS pers HeaderLoadsRel st lst (header_fixpoint inst fsv pk pers st.store sp_dirs is_module imports)
      (Arena.Frontend.Olean.headerFixpoint fs (absPins pk) (absRoots sp_dirs) is_module
        (absImports imports)) := by
  intro hrel hinv a s2 h
  rw [header_fixpoint] at h
  peel h as q, hq
  obtain ⟨sp, stack1⟩ := q
  have hS := lv_push_imports_eq (StackRel.empty absLvWork _) hq
  rw [List.append_nil] at hS
  peel h as ls, hls
  peel h as q2, hq2
  obtain ⟨r, ar1⟩ := q2
  cases r with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok st1 =>
    peel h as hl, hhl
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    have eg : (decide ¬is_module = true) = !is_module := by cases is_module <;> rfl
    rw [eg] at hq2
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ :=
      levels_go_refines (st := st) (lst := lst) hfs (!is_module) hS (lv_state_empty_rel hls) hrel hinv _ _ hq2
    refine ⟨_, lst1, ?_, header_loads_of_eq hR hhl, hrel1, hinv1⟩
    rw [Arena.Frontend.Olean.headerFixpoint]
    exact am_bind_ok hx

end walk

/-! ## The `ModSet` operations -/

section ModSet
open ConLeche.Frontend.Olean (ModSet)

theorem absChunk_size' (s : alloc.vec.Vec Std.U8) : (absChunk s).size = s.val.length := by
  simp [absChunk, ByteArray.size]

theorem absChunk_get! (s : alloc.vec.Vec Std.U8) (k : Nat) :
    (absChunk s).get! k = if h : k < s.val.length then absByte s.val[k] else 0 := by
  simp only [absChunk, ByteArray.get!]
  split
  · next h => simp [h]
  · next h => simp [h]; rfl

theorem absChunk_set (s : alloc.vec.Vec Std.U8) (k : Std.Usize) (x : Std.U8) :
    absChunk (alloc.vec.Vec.set s k x) = (absChunk s).set! k.val (absByte x) := by
  simp [absChunk, ByteArray.set!, alloc.vec.Vec.set, List.map_set]

theorem cast_usize_fit {x : Std.U64} {b : Std.Usize} (hx : x.val ≤ Std.Usize.max)
    (h : lift (UScalar.cast .Usize x) = (ok b : Result Std.Usize)) : b.val = x.val := by
  rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hx]
  exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective h).symm

theorem cast_u8_lt8 {x : Std.U64} {b : Std.U8} (hx : x.val < 8)
    (h : lift (UScalar.cast .U8 x) = (ok b : Result Std.U8)) : b.val = x.val := by
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have : (2 : Nat) ^ UScalarTy.U8.numBits = 256 := rfl
  omega

theorem shr_val {x y z : Std.U8} (hy : y.val < 8) (h : x >>> y = ok z) : z.val = x.val >>> y.val := by
  have := UScalar.ShiftRight_spec x y (by simpa using hy)
  rw [h, Aeneas.Std.WP.spec_ok] at this
  exact this.1

theorem shl_val {x y z : Std.U8} (hy : y.val < 8) (h : x <<< y = ok z) :
    z.val = (x.val <<< y.val) % 256 := by
  have := UScalar.ShiftLeft_spec x y 256 (by simpa using hy) (by simp [U8.size, U8.numBits])
  rw [h, Aeneas.Std.WP.spec_ok] at this
  exact this.1

/-- **`mod_set_has` is `ModSet.has`**, at a position whose byte index fits a `usize`. -/
theorem mod_set_has_eq {s : alloc.vec.Vec Std.U8} {i : Std.U64} {o : Bool}
    (hi : i.val / 8 ≤ Std.Usize.max) (h : mod_set_has s i = ok o) :
    o = ModSet.has (absChunk s) i.val := by
  rw [mod_set_has] at h
  peel h as i1, hi1
  have e1 : i1.val = i.val / 8 := ConRon.Refine.Nat.udiv_val hi1
  peel h as b, hb
  have eb : b.val = i.val / 8 := by rw [cast_usize_fit (by omega) hb, e1]
  unfold ModSet.has
  rw [absChunk_get!]
  by_cases hlt : b < alloc.vec.Vec.len s
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val / 8 < s.val.length := by
      have : b.val < (alloc.vec.Vec.len s).val := hlt
      rw [vec_len_val] at this; omega
    simp only [hlt', ↓reduceDIte]
    peel h as i3, hi3
    obtain ⟨_, rfl⟩ := vec_index_eq hi3
    peel h as i4, hi4
    have e4 : i4.val = i.val % 8 := ConRon.Refine.Nat.urem_val hi4
    peel h as i5, hi5
    have e5 : i5.val = i.val % 8 := by rw [cast_u8_lt8 (by omega) hi5, e4]
    peel h as i6, hi6
    have e6 := shr_val (by omega) hi6
    peel h as i7, hi7
    simp only [lift, Result.ok.injEq] at hi7
    subst hi7
    cases Result.ok_injective h
    simp only [eb] at e6
    have key : ∀ (u : Std.U8) (c : UInt8), u.val = c.toNat → (decide (u = 1#u8) = (c == 1)) := by
      intro u c hu
      by_cases hc : c = 1
      · subst hc
        have : u = 1#u8 := UScalar.eq_of_val_eq (by rw [hu]; rfl)
        simp [this]
      · have : u ≠ 1#u8 := fun he => hc (UInt8.toNat_inj.mp (by rw [← hu, he]; rfl))
        simp [this, hc]
    apply key
    rw [UScalar.val_and, UInt8.toNat_and, UInt8.toNat_shiftRight, absByte_toNat, e6, e5]
    have l1 : (1#u8 : Std.U8).val = 1 := by decide
    rw [l1]
    simp
  · rw [ite_eq_right hlt] at h
    have hlt' : ¬ i.val / 8 < s.val.length := by
      have : ¬ b.val < (alloc.vec.Vec.len s).val := hlt
      rw [vec_len_val] at this; omega
    simp only [hlt', ↓reduceDIte]
    cases Result.ok_injective h
    have z : ∀ j : UInt8, ((0 : UInt8) >>> j &&& 1 == 1) = false := by decide
    rw [z]

theorem absByte_shl1 {i6 : Std.U8} {j : Nat} (hj : j < 8) (e : i6.val = (1 <<< j) % 256) :
    absByte i6 = (1 : UInt8) <<< j.toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [absByte_toNat, e, UInt8.toNat_shiftLeft]
  simp [Nat.mod_eq_of_lt (show j < 256 by omega), Nat.mod_eq_of_lt hj]

/-- **`mod_set_add` is `ModSet.add`**, at a position whose byte index fits a `usize`. -/
theorem mod_set_add_eq {s : alloc.vec.Vec Std.U8} {i : Std.U64} {o}
    (hi : i.val / 8 ≤ Std.Usize.max) (h : mod_set_add s i = ok o) :
    absChunk o = ModSet.add (absChunk s) i.val := by
  rw [mod_set_add] at h
  peel h as i1, hi1
  have e1 : i1.val = i.val / 8 := ConRon.Refine.Nat.udiv_val hi1
  peel h as b, hb
  have eb : b.val = i.val / 8 := by rw [cast_usize_fit (by omega) hb, e1]
  unfold ModSet.add
  rw [absChunk_size']
  by_cases hlt : b < alloc.vec.Vec.len s
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val / 8 < s.val.length := by
      have : b.val < (alloc.vec.Vec.len s).val := hlt
      rw [vec_len_val] at this; omega
    simp only [hlt', ↓reduceIte]
    peel h as i3, hi3
    obtain ⟨_, rfl⟩ := vec_index_eq hi3
    peel h as i4, hi4
    have e4 : i4.val = i.val % 8 := ConRon.Refine.Nat.urem_val hi4
    peel h as i5, hi5
    have e5 : i5.val = i.val % 8 := by rw [cast_u8_lt8 (by omega) hi5, e4]
    peel h as i6, hi6
    have e6 := shl_val (by omega) hi6
    peel h as p, hp
    obtain ⟨_, back⟩ := p
    obtain ⟨-, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hp
    peel h as i7, hi7
    simp only [lift, Result.ok.injEq] at hi7
    subst hi7
    cases Result.ok_injective h
    rw [absChunk_set, absByte_or, absByte_shl1 (i6 := i6) (j := i.val % 8) (by omega) (by rw [e6, e5]; rfl), absChunk_get!]
    simp only [eb, hlt', ↓reduceDIte]
  · rw [ite_eq_right hlt] at h
    have hlt' : ¬ i.val / 8 < s.val.length := by
      have : ¬ b.val < (alloc.vec.Vec.len s).val := hlt
      rw [vec_len_val] at this; omega
    simp only [hlt', ↓reduceIte]
    cases Result.ok_injective h
    rfl

theorem mod_set_empty_loop_eq (k : Std.Usize) (s : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hs : s.val = List.replicate i.val 0#u8) (hi : i.val ≤ k.val) {o}
    (h : mod_set_empty_loop k s i = ok o) : o.val = List.replicate k.val 0#u8 := by
  rw [mod_set_empty_loop] at h
  by_cases hlt : i < k
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val < k.val := hlt
    peel h as s1, hs1
    peel h as i1, hi1
    have hi1v : i1.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi1]; rfl
    refine mod_set_empty_loop_eq k s1 i1 ?_ (by omega) h
    rw [ConRon.Refine.vec_push_val hs1, hs, hi1v, List.replicate_succ']
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : i.val = k.val := by have : ¬ i.val < k.val := hlt; omega
    rw [hs, this]
termination_by k.val - i.val
decreasing_by have : i.val < k.val := hlt; omega

/-- **`mod_set_empty` is `ModSet.empty`**, over a size whose bytes fit a `usize`. -/
theorem mod_set_empty_eq {n : Std.U64} {o} (hn : (n.val + 7) / 8 ≤ Std.Usize.max)
    (h : mod_set_empty n = ok o) : absChunk o = ModSet.empty n.val := by
  rw [mod_set_empty] at h
  peel h as i, hi
  have ei : i.val = n.val + 7 := by rw [ConRon.Refine.Nat.uadd_val hi]; rfl
  peel h as i1, hi1
  have e1 : i1.val = i.val / 8 := ConRon.Refine.Nat.udiv_val hi1
  peel h as k, hk
  have ek : k.val = (n.val + 7) / 8 := by rw [cast_usize_fit (by omega) hk, e1, ei]
  have := mod_set_empty_loop_eq k _ 0#usize (by simp [alloc.vec.Vec.with_capacity]) (by simp) h
  unfold ModSet.empty
  simp only [absChunk, this, ek, List.map_replicate]
  rfl

theorem bytearray_set!_oob {b : ByteArray} {k : Nat} {v : UInt8} (hk : b.size ≤ k) : b.set! k v = b := by
  obtain ⟨arr⟩ := b
  simp only [ByteArray.set!, ByteArray.size] at *
  congr 1
  simp [Array.set!, Array.setIfInBounds, show ¬ k < arr.size by omega]

theorem nat_fold_congr {α : Type} {n m : Nat} (g : Nat → α → α) (S : α) (h : n = m) :
    Nat.fold n (fun i _ x => g i x) S = Nat.fold m (fun i _ x => g i x) S := by
  subst h; rfl

/-- One step of `ModSet.union`. -/
@[reducible] def unionStep (T : ByteArray) (j : Nat) (x : ByteArray) : ByteArray :=
  x.set! j (x.get! j ||| T.get! j)

theorem mod_set_union_loop_eq (t s : alloc.vec.Vec Std.U8) (k : Std.Usize) (S : ByteArray)
    (hk : k.val ≤ t.val.length)
    (hs : absChunk s = Nat.fold k.val (fun j _ x => unionStep (absChunk t) j x) S) {o}
    (h : mod_set_union_loop t s k = ok o) :
    absChunk o = Nat.fold t.val.length (fun j _ x => unionStep (absChunk t) j x) S := by
  rw [mod_set_union_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len t
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < t.val.length := by
      have : k.val < (alloc.vec.Vec.len t).val := hlt
      rwa [vec_len_val] at this
    peel h as s1, hs1
    peel h as k1, hk1
    have hk1v : k1.val = k.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hk1]; rfl
    refine mod_set_union_loop_eq t s1 k1 S (by omega) ?_ h
    rw [hk1v, Nat.fold_succ, ← hs]
    show absChunk s1 = unionStep (absChunk t) k.val (absChunk s)
    by_cases hls : k < alloc.vec.Vec.len s
    · rw [ite_eq_left hls] at hs1
      have hls' : k.val < s.val.length := by
        have : k.val < (alloc.vec.Vec.len s).val := hls
        rwa [vec_len_val] at this
      peel hs1 as i2, hi2
      obtain ⟨_, rfl⟩ := vec_index_eq hi2
      peel hs1 as i3, hi3
      obtain ⟨_, rfl⟩ := vec_index_eq hi3
      peel hs1 as p, hp
      obtain ⟨_, back⟩ := p
      obtain ⟨-, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hp
      peel hs1 as i4, hi4
      simp only [lift, Result.ok.injEq] at hi4
      subst hi4
      cases Result.ok_injective hs1
      rw [absChunk_set, absByte_or, unionStep, absChunk_get!, absChunk_get!]
      simp only [hls', hlt', ↓reduceDIte]
    · rw [ite_eq_right hls] at hs1
      cases Result.ok_injective hs1
      have hls' : s.val.length ≤ k.val := by
        have : ¬ k.val < (alloc.vec.Vec.len s).val := hls
        rw [vec_len_val] at this; omega
      rw [unionStep, bytearray_set!_oob (by rw [absChunk_size']; exact hls')]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : k.val = t.val.length := by
      have : ¬ k.val < (alloc.vec.Vec.len t).val := hlt
      rw [vec_len_val] at this; omega
    rw [hs]
    exact nat_fold_congr _ _ this
termination_by t.val.length - k.val
decreasing_by
  have : k.val < (alloc.vec.Vec.len t).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`mod_set_union` is `ModSet.union`.** -/
theorem mod_set_union_eq {s t : alloc.vec.Vec Std.U8} {o} (h : mod_set_union s t = ok o) :
    absChunk o = ModSet.union (absChunk s) (absChunk t) := by
  rw [mod_set_union] at h
  have := mod_set_union_loop_eq t s 0#usize (absChunk s) (Nat.zero_le _) rfl h
  rw [this]
  unfold ModSet.union
  exact nat_fold_congr (unionStep (absChunk t)) _ (absChunk_size' t).symm

end ModSet

/-! ## The public-import closures -/

section Pub
open ConLeche.Frontend.Olean (ModSet)

/-- One import of `pubClosures`'s inner fold. -/
def pubStep (ld : Arena.Frontend.Olean.HeaderLoads) (acc : _root_.Array ModSet) (s : ModSet)
    (imp : ConLeche.Frontend.Olean.ImportF NIdx) : ModSet :=
  if !imp.isExported then s else
  match ld.index[imp.module]? with
  | some j => if j < acc.size then s.union acc[j]! else s.add j
  | none => s

/-- One module of `pubClosures`'s outer fold. -/
def pubAt (ld : Arena.Frontend.Olean.HeaderLoads) (acc : _root_.Array ModSet) (i : Nat) :
    _root_.Array ModSet :=
  acc.push (((ld.imports[i]?).getD #[]).foldl (pubStep ld acc) ((ModSet.empty ld.order.size).add i))

theorem pubClosures_eq (ld : Arena.Frontend.Olean.HeaderLoads) :
    Arena.Frontend.Olean.pubClosures ld =
      (List.range ld.order.size).foldl (pubAt ld) (_root_.Array.mkEmpty ld.order.size) := rfl

/-- The twin's load positions are positions of its order. -/
abbrev IndexFits (ld : Arena.Frontend.Olean.HeaderLoads) : Prop :=
  ∀ (m : NIdx) (j : Nat), ld.index[m]? = some j → j < ld.order.size

theorem ofStateGo_index_lt (fm : _root_.Std.HashMap NIdx ConLeche.Frontend.Olean.LoadFlags) :
    ∀ (ms : List NIdx) (i : Nat) im fl is (ix : _root_.Std.HashMap NIdx Nat),
      (∀ (m : NIdx) (j : Nat), ix[m]? = some j → j < i) →
      ∀ (m : NIdx) (j : Nat), (Arena.Frontend.Olean.HeaderLoads.ofStateGo fm ms i im fl is ix).2.2[m]? = some j →
        j < i + ms.length := by
  intro ms
  induction ms with
  | nil => intro i im fl is ix hix m j h; simpa using hix m j h
  | cons x ms ih =>
    intro i im fl is ix hix m j h
    rw [Arena.Frontend.Olean.HeaderLoads.ofStateGo] at h
    have := ih (i + 1) _ _ _ _ (fun m' j' h' => by
      rw [_root_.Std.HashMap.getElem?_insert] at h'
      split at h'
      · cases h'; omega
      · have := hix m' j' h'; omega) m j h
    simp only [List.length_cons]; omega

/-- **`HeaderLoads.ofState`'s positions fit its order.** -/
theorem ofState_index_fits (st : Arena.Frontend.Olean.LvState) :
    IndexFits (Arena.Frontend.Olean.HeaderLoads.ofState st) := by
  intro m j h
  have := ofStateGo_index_lt st.flags st.order.toList 0 st.imports #[] #[] {}
    (fun m j h => by simp at h) m j h
  simpa [Arena.Frontend.Olean.HeaderLoads.ofState] using this

/-- The relation of the closures computed so far. -/
abbrev AccA (acc : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (A : _root_.Array ModSet) : Prop :=
  acc.val.map absChunk = A.toList

theorem order_fits {ld : frontend.olean.levels.HeaderLoads} {ld' : Arena.Frontend.Olean.HeaderLoads}
    (hR : HeaderLoadsRel ld ld') : ld'.order.size = ld.order.val.length ∧ ld.order.val.length ≤ Std.Usize.max := by
  refine ⟨?_, ld.order.property⟩
  rw [← _root_.Array.length_toList, ← hR.order, List.length_map]

/-- **`pub_closure_step` is `pubStep`.** -/
theorem pub_closure_step_eq {ld : frontend.olean.levels.HeaderLoads} {ld' : Arena.Frontend.Olean.HeaderLoads}
    (hR : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    {acc : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {A : _root_.Array ModSet} (ha : AccA acc A)
    {s : alloc.vec.Vec Std.U8} {imp : frontend.olean.spec.ImportF arena.handle.NIdx} {o}
    (h : pub_closure_step ld acc s imp = ok o) :
    absChunk o = pubStep ld' A (absChunk s) (absImportF absNIdx imp) := by
  rw [pub_closure_step] at h
  unfold pubStep
  by_cases he : imp.is_exported = true
  · rw [ite_eq_left he] at h
    simp only [absImportF, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    peel h as r, hr
    have er := hR.index.get_eq hr
    rw [← er]
    cases r with
    | none => cases Result.ok_injective h; rfl
    | some j =>
      dsimp only at h ⊢
      have hjl : j.val < ld.order.val.length := by
        have := hw _ _ er.symm
        rw [(order_fits hR).1] at this; exact this
      have hjm : j.val ≤ Std.Usize.max := by have := (order_fits hR).2; omega
      have hAs : A.size = acc.val.length := by
        rw [← _root_.Array.length_toList, ← ha, List.length_map]
      peel h as i, hi
      have ei := cast_usize_fit hjm hi
      by_cases hlt : i < alloc.vec.Vec.len acc
      · rw [ite_eq_left hlt] at h
        have hlt' : j.val < acc.val.length := by
          have : i.val < (alloc.vec.Vec.len acc).val := hlt
          rw [vec_len_val] at this; omega
        simp only [Option.map_some, show j.val < A.size by omega, ↓reduceIte]
        peel h as i2, hi2
        have ei2 := cast_usize_fit hjm hi2
        peel h as v, hv
        obtain ⟨hb, rfl⟩ := vec_index_eq hv
        rw [mod_set_union_eq h]
        congr 1
        have eA : A = (acc.val.map absChunk).toArray := by
          apply _root_.Array.ext'; rw [← ha]
        subst eA
        simp [ei2, hlt']
      · rw [ite_eq_right hlt] at h
        have hlt' : ¬ j.val < acc.val.length := by
          have : ¬ i.val < (alloc.vec.Vec.len acc).val := hlt
          rw [vec_len_val] at this; omega
        simp only [Option.map_some, show ¬ j.val < A.size by omega, ↓reduceIte]
        exact mod_set_add_eq (by omega) h
  · rw [ite_eq_right he] at h
    cases Result.ok_injective h
    have : imp.is_exported = false := by simpa using he
    simp [absImportF, this]

theorem pub_closure_at_loop_eq {ld : frontend.olean.levels.HeaderLoads}
    {ld' : Arena.Frontend.Olean.HeaderLoads} (hR : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    {acc : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {A : _root_.Array ModSet} (ha : AccA acc A)
    (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    (s : alloc.vec.Vec Std.U8) (k : Std.Usize) {o}
    (h : pub_closure_at_loop ld.order ld.flags ld.imports ld.index acc s imps k = ok o) :
    absChunk o = ((imps.val.drop k.val).map (absImportF absNIdx)).foldl (pubStep ld' A) (absChunk s) := by
  rw [pub_closure_at_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len imps
  · rw [ite_eq_left hlt] at h
    have hlt' : k.val < imps.val.length := by
      have : k.val < (alloc.vec.Vec.len imps).val := hlt
      rwa [vec_len_val] at this
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel h as s1, hs1
    have e1 := pub_closure_step_eq hR hw ha hs1
    peel h as k1, hk1
    have hk1v : k1.val = k.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hk1]; rfl
    have ih := pub_closure_at_loop_eq hR hw ha imps s1 k1 h
    rw [ih, hk1v, e1, List.drop_eq_getElem_cons hlt', List.map_cons, List.foldl_cons]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : imps.val.length ≤ k.val := by
      have : ¬ k.val < (alloc.vec.Vec.len imps).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le hle]; rfl
termination_by imps.val.length - k.val
decreasing_by
  have : k.val < (alloc.vec.Vec.len imps).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`pub_closure_at` is one module of `pubClosures`.** -/
theorem pub_closure_at_eq {ld : frontend.olean.levels.HeaderLoads}
    {ld' : Arena.Frontend.Olean.HeaderLoads} (hR : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    {acc : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {A : _root_.Array ModSet} (ha : AccA acc A)
    {i : Std.Usize} {o} (h : pub_closure_at ld acc i = ok o) :
    absChunk o = ((ld'.imports[i.val]?).getD #[]).foldl (pubStep ld' A)
      ((ModSet.empty ld'.order.size).add i.val) := by
  rw [pub_closure_at] at h
  obtain ⟨eo, hmax⟩ := order_fits hR
  peel h as n, hn
  have en : n.val = ld.order.val.length := by
    simp only [lift, Result.ok.injEq] at hn
    subst hn
    rw [usize_cast_u64_val', vec_len_val]
  peel h as v, hv
  have ev := mod_set_empty_eq (by omega) hv
  peel h as i2, hi2
  have ei2 : i2.val = i.val := by
    simp only [lift, Result.ok.injEq] at hi2
    subst hi2
    rw [usize_cast_u64_val']
  peel h as s, hs
  have es := mod_set_add_eq (by have := i.hBounds; rw [ei2]; scalar_tac) hs
  rw [ev, en, ei2, ← eo] at es
  have eI : ld'.imports[i.val]? = (ld.imports.val.map absImports)[i.val]? := by
    rw [hR.imports]; simp
  by_cases hlt : i < alloc.vec.Vec.len ld.imports
  · rw [ite_eq_left hlt] at h
    peel h as imps, himps
    obtain ⟨hb, rfl⟩ := vec_index_eq himps
    rw [pub_closure_at_loop_eq hR hw ha _ s _ h, eI, List.getElem?_map, List.getElem?_eq_getElem hb]
    simp [absImports, es]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : ld.imports.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len ld.imports).val := hlt
      rw [vec_len_val] at this; omega
    rw [eI, List.getElem?_eq_none (by simpa using hle)]
    simpa using es

theorem pub_closures_loop_eq {ld : frontend.olean.levels.HeaderLoads}
    {ld' : Arena.Frontend.Olean.HeaderLoads} (hR : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    (n : Std.Usize) (acc : alloc.vec.Vec (alloc.vec.Vec Std.U8)) {A : _root_.Array ModSet}
    (ha : AccA acc A) (i : Std.Usize) {o}
    (h : pub_closures_loop ld.order ld.flags ld.imports ld.index n acc i = ok o) :
    AccA o ((List.range' i.val (n.val - i.val)).foldl (pubAt ld') A) := by
  rw [pub_closures_loop] at h
  by_cases hlt : i < n
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val < n.val := hlt
    peel h as s, hs
    have es := pub_closure_at_eq hR hw ha hs
    peel h as acc1, hacc1
    peel h as i1, hi1
    have hi1v : i1.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi1]; rfl
    have ha1 : AccA acc1 (pubAt ld' A i.val) := by
      show acc1.val.map absChunk = _
      rw [ConRon.Refine.vec_push_val hacc1, List.map_append, ha, pubAt, List.map_singleton, es]
      simp
    have ih := pub_closures_loop_eq hR hw n acc1 ha1 i1 h
    rw [hi1v] at ih
    have e : n.val - i.val = (n.val - (i.val + 1)) + 1 := by omega
    rw [e, List.range'_succ, List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : n.val - i.val = 0 := by have : ¬ i.val < n.val := hlt; omega
    rw [this]
    exact ha
termination_by n.val - i.val
decreasing_by have : i.val < n.val := hlt; omega

/-- **`pub_closures` is `pubClosures`**, on loads whose positions fit their order
(`ofState_index_fits`). -/
theorem pub_closures_eq {ld : frontend.olean.levels.HeaderLoads}
    {ld' : Arena.Frontend.Olean.HeaderLoads} (hR : HeaderLoadsRel ld ld') (hw : IndexFits ld') {o}
    (h : pub_closures ld = ok o) : AccA o (Arena.Frontend.Olean.pubClosures ld') := by
  rw [pub_closures] at h
  have := pub_closures_loop_eq hR hw _ _ (A := #[]) (by simp [AccA, alloc.vec.Vec.with_capacity]) _ h
  rw [pubClosures_eq, List.range_eq_range', (order_fits hR).1]
  simpa [vec_len_val] using this

end Pub

end ConRon.Refine2.Frontend.Olean

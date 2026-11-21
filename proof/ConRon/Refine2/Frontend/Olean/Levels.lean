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

variable {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
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

end walk

end ConRon.Refine2.Frontend.Olean

/-
# `ConRon.Refine2.Modular.ReachRel` — the relations of the reach's types

**Task #166, Theorem 2.**  The abstractions of `modular/reach.rs`'s types against the twin's
(`Arena/Modular/Reach.lean`), shared by every Theorem-2 file of the reach.

* A `PartKey` is the twin's (`absPartKey`): its `Hashable`/`Eq2`/`Dup` instances are the twin's
  derived `Hashable`/`BEq` and the identity (`partKey_eq2`, `partKey_dup2_ok`).  A `HashMap2`
  keyed by part keys is a `Std.HashMap PartKey` (`PMapRel`), one keyed by name handles with
  related (not abstracted) values an `NMapR`.
* A `Spot` is the twin's (`absSpot`), a `ProofStatus` the twin's (`absProofStatus`).
* A `PartRead` (the files, the view's bytes, the region, the memo) is the twin's
  `Region × SM` (`PartReadRel`): the region the view's bytes cut, which fits them, and the memo
  by `SMRel`.
* `ReachEnvRel`: the Rust's `module`, `copies` and the separate `wr`, `own` parameters against
  the twin's `ReachEnv`.
* `ReachCacheRel`: every map of the caches; `pending` related up to its message.
* `ReachLogRel`: the sets, the records, and the stack (`StackRel`: the live prefix reversed).
-/
import ConRon.Refine2.Frontend.Olean.Index
import ConRon.Refine2.Frontend.Olean.Present
import ConRon.Arena.Modular.Reach

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Refine.HashMap (Eq2Fwd)
open ConLeche.Frontend.Olean (OLeanLevel)

/-! ## Levels -/

/-- Part keys' equality, for the `HashMap2` lemmas (a name handle's is classical). -/
noncomputable instance : DecidableEq frontend.modular.reach.PartKey := Classical.decEq _

/-- `level_index`'s word, as a number. -/
def levelIdx : frontend.olean.view.OLeanLevel → Nat
  | .Exported => 0
  | .Server => 1
  | .Private => 2

/-- **`level_index` is the constructor's index.** -/
theorem level_index_val {l : frontend.olean.view.OLeanLevel} {i : Std.U64}
    (h : frontend.modular.reach.level_index l = ok i) : i.val = levelIdx l := by
  cases l <;> cases Result.ok_injective h <;> rfl

theorem levelIdx_inj {a b : frontend.olean.view.OLeanLevel} (h : levelIdx a = levelIdx b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem absLevel_inj : Function.Injective absLevel := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **`level_dup` is the identity.** -/
theorem level_dup_ok {l x : frontend.olean.view.OLeanLevel}
    (h : frontend.modular.reach.level_dup l = ok x) : x = l := by
  cases l <;> exact (Result.ok_injective h).symm

/-! ## Part keys -/

/-- **`PartKey`, as the twin's.** -/
@[reducible] def absPartKey (k : frontend.modular.reach.PartKey) : ConRon.Arena.Modular.PartKey :=
  ⟨absNIdx k.module, absLevel k.level⟩

theorem absPartKey_inj : Function.Injective absPartKey := by
  intro a b h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [absPartKey, ConRon.Arena.Modular.PartKey.mk.injEq] at h
  rw [absNIdx_inj h.1, absLevel_inj h.2]

theorem partKey_beq_iff (a b : ConRon.Arena.Modular.PartKey) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq ConRon.Arena.Modular.PartKey where
  eq_of_beq h := (partKey_beq_iff _ _).1 h
  rfl := (partKey_beq_iff _ _).2 rfl

/-- The hash of part keys. -/
abbrev hPK := frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapHashable
/-- The equality of part keys. -/
abbrev ePK := frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapEq2

/-- **`PartKey`'s `eq2` is equality.** -/
theorem partKey_eq2 : Eq2Fwd ePK (fun _ => True) := by
  intro a b c _ _ h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  change frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapEq2.eq2 _ _ = ok c at h
  rw [frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  obtain ⟨b0, hb0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e0 := nidx_eq2 a1 b1 b0 trivial trivial hb0
  subst e0
  by_cases e : a1 = b1
  · subst e
    simp only [decide_true, ↓reduceIte] at h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have v1 := level_index_val hi1
    have v2 := level_index_val hi2
    by_cases el : a2 = b2
    · subst el
      have : i1 = i2 := UScalar.eq_of_val_eq (by rw [v1, v2])
      simp [this]
    · have : i1 ≠ i2 := fun he => el (levelIdx_inj (by rw [← v1, ← v2, he]))
      simp [this, el]
  · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases Result.ok_injective h
    simp [e]

/-- **`PartKey`'s `dup2` is the identity.** -/
theorem partKey_dup2_ok {k x : frontend.modular.reach.PartKey}
    (h : frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapDup.dup2 k = ok x) : x = k := by
  rw [frontend.modular.reach.PartKey.Insts.Con_ron_coreRonHashmapDup.dup2] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn, level_dup_ok hl]

/-- **`priv_key` is `privKey`.** -/
theorem priv_key_eq {m : arena.handle.NIdx} {k : frontend.modular.reach.PartKey}
    (h : frontend.modular.reach.priv_key m = ok k) :
    k = ⟨m, .Private⟩ ∧ absPartKey k = ConRon.Arena.Modular.privKey (absNIdx m) := by
  rw [frontend.modular.reach.priv_key] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn]
  exact ⟨rfl, rfl⟩

/-! ## Spots -/

/-- **`Spot`, as the twin's.** -/
@[reducible] def absSpot (s : frontend.modular.reach.Spot) : ConRon.Arena.Modular.Spot :=
  ⟨absPartKey s.part, absNamePosition s.pos⟩

/-- **`name_position_dup` is the identity.** -/
theorem name_position_dup_ok {q x : frontend.olean.reads.NamePosition}
    (h : frontend.modular.reach.name_position_dup q = ok x) : x = q := by
  rw [frontend.modular.reach.name_position_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [nidx_dup2_ok hn]

/-- **`spot_dup` is the identity.** -/
theorem spot_dup_ok {s x : frontend.modular.reach.Spot}
    (h : frontend.modular.reach.spot_dup s = ok x) : x = s := by
  rw [frontend.modular.reach.spot_dup] at h
  obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [partKey_dup2_ok hk, name_position_dup_ok hq]

/-! ## Proof statuses -/

/-- **`ProofStatus`, as the twin's.** -/
def absProofStatus : frontend.modular.reach.ProofStatus → ConRon.Arena.Modular.ProofStatus
  | .Yes => .yes
  | .No => .no
  | .Infer => .infer

/-! ## Tables keyed by part keys -/

/-- **A `HashMap2` keyed by part keys**, as a `Std.HashMap` of the twin's keys, the values
related by `R`. -/
structure PMapRel {V V' : Type} (R : V → V' → Prop)
    (m : ron.hashmap2.HashMap2 frontend.modular.reach.PartKey V)
    (s : _root_.Std.HashMap ConRon.Arena.Modular.PartKey V') : Prop where
  inv : Inv hPK m
  get : ∀ k, Option.Rel R (toFun m k) s[absPartKey k]?

section PMapRel
variable {V V' : Type} {R : V → V' → Prop} {m : ron.hashmap2.HashMap2 frontend.modular.reach.PartKey V}
  {s : _root_.Std.HashMap ConRon.Arena.Modular.PartKey V'}

theorem PMapRel.get_eq (h : PMapRel R m s) {k : frontend.modular.reach.PartKey} {o : Option V}
    (hg : ron.hashmap2.HashMap2.get hPK ePK m k = ok o) : Option.Rel R o s[absPartKey k]? := by
  rw [ConRon.Refine.HashMap2.get_refines_gen partKey_eq2 h.inv (fun _ _ => trivial) trivial hg]
  exact h.get k

theorem PMapRel.contains_eq (h : PMapRel R m s) {k : frontend.modular.reach.PartKey} {b : Bool}
    (hg : ron.hashmap2.HashMap2.contains_key hPK ePK m k = ok b) : b = s.contains (absPartKey k) := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen partKey_eq2 h.inv (fun _ _ => trivial) trivial hg,
    _root_.Std.HashMap.contains_eq_isSome_getElem?]
  have hg := h.get k
  generalize toFun m k = a at hg ⊢
  generalize s[absPartKey k]? = b at hg ⊢
  cases hg <;> rfl

theorem PMapRel.insert (h : PMapRel R m s) {k : frontend.modular.reach.PartKey} {v : V} {v' : V'}
    (hv : R v v') {old} {m'} (hi : ron.hashmap2.HashMap2.insert hPK ePK m k v = ok (old, m')) :
    PMapRel R m' (s.insert (absPartKey k) v') := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen partKey_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k1 = k
  · subst hk; simpa using Option.Rel.some hv
  · have hne : (absPartKey k == absPartKey k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absPartKey_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem PMapRel.remove (h : PMapRel R m s) {k : frontend.modular.reach.PartKey} {old} {m'}
    (hi : ron.hashmap2.HashMap2.remove hPK ePK m k = ok (old, m')) :
    Option.Rel R old s[absPartKey k]? ∧ PMapRel R m' (s.erase (absPartKey k)) := by
  obtain ⟨hinv, hold, hupd, -⟩ := ConRon.Refine.HashMap2.remove_refines_gen partKey_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨by rw [hold]; exact h.get k, hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_erase]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (absPartKey k == absPartKey k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absPartKey_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem PMapRel.new (hn : ron.hashmap2.HashMap2.new frontend.modular.reach.PartKey V = ok m) :
    PMapRel R m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hPK) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

end PMapRel

/-! ## Tables keyed by name handles, the values related -/

/-- **A `HashMap2` keyed by name handles**, as a `Std.HashMap` of what they stand for, the
values related by `R` (`NMapRel` with a relation for the abstraction). -/
structure NMapR {V V' : Type} (R : V → V' → Prop) (m : ron.hashmap2.HashMap2 arena.handle.NIdx V)
    (s : _root_.Std.HashMap NIdx V') : Prop where
  inv : Inv hN m
  get : ∀ k, Option.Rel R (toFun m k) s[absNIdx k]?

section NMapR
variable {V V' : Type} {R : V → V' → Prop} {m : ron.hashmap2.HashMap2 arena.handle.NIdx V}
  {s : _root_.Std.HashMap NIdx V'}

theorem NMapR.get_eq (h : NMapR R m s) {k : arena.handle.NIdx} {o : Option V}
    (hg : ron.hashmap2.HashMap2.get hN eN m k = ok o) : Option.Rel R o s[absNIdx k]? := by
  rw [ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 h.inv (fun _ _ => trivial) trivial hg]
  exact h.get k

theorem NMapR.contains_eq (h : NMapR R m s) {k : arena.handle.NIdx} {b : Bool}
    (hg : ron.hashmap2.HashMap2.contains_key hN eN m k = ok b) : b = s.contains (absNIdx k) := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen nidx_eq2 h.inv (fun _ _ => trivial) trivial hg,
    _root_.Std.HashMap.contains_eq_isSome_getElem?]
  have hg := h.get k
  generalize toFun m k = a at hg ⊢
  generalize s[absNIdx k]? = b at hg ⊢
  cases hg <;> rfl

theorem NMapR.insert (h : NMapR R m s) {k : arena.handle.NIdx} {v : V} {v' : V'}
    (hv : R v v') {old} {m'} (hi : ron.hashmap2.HashMap2.insert hN eN m k v = ok (old, m')) :
    NMapR R m' (s.insert (absNIdx k) v') := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k1 = k
  · subst hk; simpa using Option.Rel.some hv
  · have hne : (absNIdx k == absNIdx k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absNIdx_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem NMapR.new (hn : ron.hashmap2.HashMap2.new arena.handle.NIdx V = ok m) : NMapR R m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hN) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

end NMapR

/-! ## A part's read -/

/-- **A part's files, view and memo, as the twin's `Region × SM`**: the region the view's bytes
cut, which fits them, and the memo. -/
structure PartReadRel (p : frontend.modular.reach.PartRead)
    (q : ConLeche.Frontend.Olean.Region × TSM) : Prop where
  region : ∀ bs, frontend.olean.view.view_bytes p.files p.vb = ok bs →
    q.1 = absRegion bs p.region ∧ RegionFits bs p.region
  memo : SMRel p.memo q.2

/-! ## The environment -/

/-- A clashing name's copies, as the twin's. -/
@[reducible] def absCopies (v : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.spec.StmtRec)) :
    _root_.Array (NIdx × Arena.Frontend.Olean.StmtRec) :=
  (v.val.map fun p => (absNIdx p.1, absStmtRec p.2)).toArray

/-- **`ReachEnv` and the separate `wr`, `own` parameters, against the twin's `ReachEnv`.** -/
structure ReachEnvRel (env : frontend.modular.reach.ReachEnv) (wr : frontend.olean.index.WorkerReads)
    (own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool) (env' : ConRon.Arena.Modular.ReachEnv) :
    Prop where
  mod : env'.mod = absNIdx env.module
  wr : WorkerReadsRel wr env'.wr
  /-- the load positions are positions of the load order (`headerFixpoint_fits`), so the
  Rust's `as usize` of one keeps it -/
  fits : IndexFits env'.wr.loads
  own : NSet own env'.own
  copies : NMapRel absCopies env.copies env'.copies

/-! ## The caches -/

/-- A pair of names, as the twin's. -/
@[reducible] def absNN (p : arena.handle.NIdx × arena.handle.NIdx) : NIdx × NIdx :=
  (absNIdx p.1, absNIdx p.2)

/-- A recursor block's locations, as the twin's. -/
@[reducible] def absLocs (v : alloc.vec.Vec Std.U64) : _root_.Array Nat := (v.val.map (·.val)).toArray

/-- **A pending statement**: the name and the statement as the twin's, the message unrelated. -/
def PendingRel (a : alloc.vec.Vec Std.U32 × arena.handle.NIdx × frontend.olean.spec.StmtRec)
    (b : String × NIdx × Arena.Frontend.Olean.StmtRec) : Prop :=
  b.2.1 = absNIdx a.2.1 ∧ b.2.2 = absStmtRec a.2.2

/-- **The reach's caches against the twin's**, map by map. -/
structure ReachCacheRel (c : frontend.modular.reach.ReachCache) (c' : ConRon.Arena.Modular.ReachCache) :
    Prop where
  tables : PMapRel (EqA absNamePositions) c.tables c'.tables
  looks : PMapRel (NMapRel absNamePosition) c.looks c'.looks
  parts : PMapRel PartReadRel c.parts c'.parts
  recBlocks : PMapRel (NMapRel absLocs) c.rec_blocks c'.recBlocks
  views : NMapR (NMapRel absSpot) c.views c'.views
  located : NMapRel absSpot c.located c'.located
  completed : c.completed.val.map absNN = c'.completed.toList
  pending : List.Forall₂ PendingRel c.pending.val c'.pending.toList
  partners : c.partners.val.map absNN = c'.partners.toList
  searches : c.searches.val = c'.searches

/-- **`reach_cache_empty` is the twin's `{}`.** -/
theorem reach_cache_empty_rel {c} (h : frontend.modular.reach.reach_cache_empty = ok c) :
    ReachCacheRel c {} := by
  rw [frontend.modular.reach.reach_cache_empty] at h
  obtain ⟨h1, hh1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨h2, hh2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨h3, hh3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨h4, hh4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨h5, hh5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨h6, hh6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  exact ⟨PMapRel.new hh1, PMapRel.new hh2, PMapRel.new hh3, PMapRel.new hh4, NMapR.new hh5,
    NMapRel.new hh6, rfl, List.Forall₂.nil, rfl, rfl⟩

/-! ## The worklist -/

/-- **The reach's logical state against the twin's**: the sets, the records, and the stack
(its live prefix, reversed, the twin's list, top first). -/
structure ReachLogRel (l : frontend.modular.reach.ReachLog) (L : ConRon.Arena.Modular.ReachLog) :
    Prop where
  seen : NSet l.seen L.seen
  stored : NSet l.stored L.stored
  ctx : l.ctx.val.map absIDeclaration = L.ctx.toList
  homes : l.homes.val.map absNIdx = L.homes.toList
  reads : l.reads.val.map (fun v => v.val.map absNIdx) = L.reads.toList
  stack : StackRel absNIdx l.stack l.sp L.stack

/-! ## The judgement of a cache-threading function -/

/-- **The accept of a function that threads the state and the caches** (`&mut AState`,
`&mut ReachCache`): the Rust's `Ok a` with its final state `st'` and caches `c'` is a run of
the twin, in related states, its answer related to `a` and `c'` by `R`.  An `Err` claims
nothing (`AS` with the whole state and the caches). -/
def ACS {α β : Type} (pers : arena.store.PersTier)
    (R : α → frontend.modular.reach.ReachCache → β → Prop) (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState ×
      frontend.modular.reach.ReachCache))
    (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a st' c', m = ok (.Ok a, st', c') →
      ∃ b lst', x.run lst = .ok (b, lst') ∧ R a c' b ∧
        AStateRel₀ pers st' lst' ∧ AStateInv pers st'

/-! ## The reach -/

/-- **`Reach` against the twin's**, field by field, `pending` up to its messages (the shape lane
L3's worker reads: `Refine2/Modular/WorkerRead.lean`). -/
structure ReachRel (r : frontend.modular.reach.Reach) (r' : ConRon.Arena.Modular.Reach) : Prop where
  ctx : r'.ctx = ConRon.Refine2.Frontend.absIDeclArr r.ctx
  homes : r'.homes = ConRon.Refine2.Frontend.absNIdxArr r.homes
  completed : r'.completed = (r.completed.val.map absNN).toArray
  searches : r'.searches = r.searches.val
  inferred : r'.inferred = r.inferred.val
  pending : List.Forall₂ PendingRel r.pending.val r'.pending.toList

end ConRon.Refine2.Modular

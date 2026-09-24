/-
# `ConRon.Refine2.Frontend.Prepare` — `crates/con-ron-core/src/frontend/prepare.rs`

**Task #97-P5-Frontend.**  The stream's preparation: the prelude's records
first (the stream's own copies where it has them), the rest of the stream
after them.  Eleven `pub fn`s.

## The mask deviation, and how it is stated

con-leche's `frontOf` *erases* a picked record from the array and recurses on
what is left; the Aeneas subset cannot take an element out of a `Vec`, so the
port keeps a `picked : Vec<bool>` MASK and a `picks : Vec<usize>` PLAN and
materialises both in one pass (`prepare.rs`'s own deviation, inherited from
`con_ron_core::frontend::prepare` at task #37).  Five of the eleven functions
— `pick_idx`, `no_picks`, `front_of`, `prepared_front`, `prepared_rest`,
`prepared_stream` — are that machinery and have no twin at all.

The answer is a twin-side transcription of what the plan MEANS — `pickL`,
`restL`, `frontL` (list recursions) and `pickIdx`/`preparedFront`/
`preparedRest`/`preparedStream` over them — and ONE fact tying it to the twin's
erase-and-recurse: **`pick_preparedRest`**, *erasing the first hit from the
unmasked records is masking it* (`restL_pick`, by induction on the stream).
With it `front_of_loop_refines` runs the port's loop and the twin's `frontOf`
in lockstep: the twin's accumulator is `preparedFront` of the plan so far and
the twin's remaining array is `preparedRest` of the mask so far.

Task #97-P5-Front replaced the previous `preparedStream_eq_frontOf`, which was
**false as stated** (its `picks`/`picked` were universally quantified and tied
to nothing, and it prepended the accumulator twice), and restated
`front_of_refines` from a success-only claim to a full `Sim` whose value is
the front and rest the plan stands for (`absPlan`) and whose `WF` is the plan's
shape (`PlanWF`) — which `prepared_front_refines` needs as `hlen`: over a plan
longer than the prelude the port reads `ps.len()` slots where the
transcription reads all of them.

`prepare_d`/`prepare_prelude` moved to `Top.lean`: they run the hoist and
`export_c::sat_sub`, both above this file.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Types

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend

/-! ## The prelude index and the prepared stream -/

def absPreludeIx (p : frontend.prepare.PreludeIx) : PreludeIx :=
  ⟨absIDeclArr p.decls⟩

def absPrepared (p : frontend.prepare.Prepared) : Prepared :=
  ⟨absIDeclArr p.decls, absU p.synthesised, absNIdxArr p.hoisted⟩

attribute [simp] absPreludeIx absPrepared

/-! ## The twin-side transcription of the port's plan

Read against `Arena/Frontend/Prepare.lean:77-101` (`pick`, `frontOf`).  The
transcriptions are list recursions (task #97-P5-Front): `pickL` is "the first
unmasked record the predicate holds of, or the length", `restL` is "the
unmasked records, in order", `frontL` is "slot `j` is the stream's own copy
where the plan found one, the prelude's own where it did not".  The one fact
that ties them to the twin's erase-and-recurse is `pick_preparedRest` below:
*erasing the first hit from the unmasked records is masking it*. -/

/-- The unmasked records of a stream, in order: `prepared_rest`'s meaning. -/
def restL : List IDeclaration → List Bool → List IDeclaration
  | [], _ => []
  | d :: ds, m => if m.headD false then restL ds m.tail else d :: restL ds m.tail

/-- The index of the first unmasked record `p` holds of, or the length:
`pick_idx`'s meaning. -/
def pickL (p : IDeclaration → Bool) : List IDeclaration → List Bool → Nat
  | [], _ => 0
  | d :: ds, m => if !m.headD false && p d then 0 else pickL p ds m.tail + 1

/-- Slot by slot, the front: `prepared_front`'s meaning, from slot `j`. -/
def frontL (ps ds : Array IDeclaration) : List Nat → Nat → List IDeclaration
  | [], _ => []
  | k :: ks, j => ds[k]?.getD (ps.getD j default) :: frontL ps ds ks (j + 1)

/-- The twin-side reading of `prepare::pick_idx`: the index of the first
record of `ds` that is not masked and declares `n`, or `ds.size`. -/
def pickIdx (n : NIdx) (ds : Array IDeclaration) (picked : List Bool) : Nat :=
  pickL (declares n) ds.toList picked

/-- The twin-side reading of `prepare::prepared_front`. -/
def preparedFront (ps ds : Array IDeclaration) (picks : List Nat) :
    Array IDeclaration :=
  (frontL ps ds picks 0).toArray

/-- The twin-side reading of `prepare::prepared_rest`. -/
def preparedRest (ds : Array IDeclaration) (picked : List Bool) :
    Array IDeclaration :=
  (restL ds.toList picked).toArray

/-- The twin-side reading of `prepare::prepared_stream`. -/
def preparedStream (ps ds : Array IDeclaration) (picks : List Nat)
    (picked : List Bool) : Array IDeclaration :=
  preparedFront ps ds picks ++ preparedRest ds picked

/-! ### The list facts -/

theorem restL_pick (p : IDeclaration → Bool) :
    ∀ (L : List IDeclaration) (M : List Bool), M.length = L.length →
      (restL L M)[(restL L M).findIdx p]? = L[pickL p L M]? ∧
      (restL L M).eraseIdx ((restL L M).findIdx p) =
        restL L (M.set (pickL p L M) true)
  | [], M, _ => by simp [restL, pickL]
  | d :: L, [], h => by simp at h
  | d :: L, m :: M, h => by
    have hl : M.length = L.length := by simpa using h
    obtain ⟨ih1, ih2⟩ := restL_pick p L M hl
    cases m with
    | true =>
      simp only [restL, pickL, List.headD_cons, List.tail_cons, if_true, Bool.not_true,
        Bool.false_and, Bool.false_eq_true, if_false, List.set_cons_succ]
      exact ⟨by simpa using ih1, ih2⟩
    | false =>
      by_cases hp : p d = true
      · simp [restL, pickL, hp, List.findIdx_cons]
      · have hp' : p d = false := by simpa using hp
        simp only [restL, pickL, List.headD_cons, List.tail_cons, Bool.false_eq_true,
          if_false, Bool.not_false, Bool.true_and, hp', List.findIdx_cons, cond_false,
          List.getElem?_cons_succ, List.set_cons_succ, List.eraseIdx_cons_succ]
        exact ⟨ih1, by rw [ih2]⟩

theorem restL_none :
    ∀ (L : List IDeclaration) (k : Nat), k = L.length →
      restL L (List.replicate k false) = L
  | [], _, _ => by simp [restL]
  | d :: L, k, hk => by
    subst hk
    simp only [List.length_cons, List.replicate_succ, restL, List.headD_cons,
      Bool.false_eq_true, if_false, List.tail_cons]
    rw [restL_none L L.length rfl]

theorem pickL_le (p : IDeclaration → Bool) :
    ∀ (L : List IDeclaration) (M : List Bool), pickL p L M ≤ L.length
  | [], _ => by simp [pickL]
  | d :: L, M => by
    have := pickL_le p L M.tail
    simp only [pickL, List.length_cons]
    split <;> omega

theorem frontL_append (ps ds : Array IDeclaration) :
    ∀ (ks : List Nat) (k j : Nat),
      frontL ps ds (ks ++ [k]) j =
        frontL ps ds ks j ++ [ds[k]?.getD (ps.getD (j + ks.length) default)]
  | [], k, j => by simp [frontL]
  | k' :: ks, k, j => by
    simp only [List.cons_append, frontL, List.length_cons, List.cons_inj_right]
    rw [frontL_append ps ds ks k (j + 1), show j + 1 + ks.length = j + (ks.length + 1) by omega]

theorem preparedFront_push (ps ds : Array IDeclaration) (ks : List Nat) (k : Nat) :
    preparedFront ps ds (ks ++ [k]) =
      (preparedFront ps ds ks).push (ds[k]?.getD (ps.getD ks.length default)) := by
  simp only [preparedFront, frontL_append, Nat.zero_add]
  simp

/-- **The twin's `pick` on the unmasked records is the port's masked pick.**
The first hit among the unmasked records is the record `pickIdx` names, and
erasing it is masking it. -/
theorem pick_preparedRest (n : NIdx) (ds : Array IDeclaration) (picked : List Bool)
    (hlen : picked.length = ds.size) :
    pick n (preparedRest ds picked) =
      (ds[pickIdx n ds picked]?,
       preparedRest ds (picked.set (pickIdx n ds picked) true)) := by
  obtain ⟨h1, h2⟩ := restL_pick (declares n) ds.toList picked (by simpa using hlen)
  simp only [pick, preparedRest, pickIdx]
  refine Prod.ext ?_ ?_
  · simp only [List.findIdx_toArray, List.getElem?_toArray]
    rw [h1]; simp
  · simp only [List.findIdx_toArray]
    rw [← h2]
    simp only [Array.eraseIdxIfInBounds, List.size_toArray, List.eraseIdx_toArray]
    split
    · rfl
    · rename_i hge
      rw [List.eraseIdx_of_length_le (by omega)]

/-! ## The eleven functions -/

/-- **`prepare::prelude_ix_empty`** — the empty prelude, the twin's field
default. -/
theorem prelude_ix_empty_refines {p : frontend.prepare.PreludeIx}
    (h : frontend.prepare.prelude_ix_empty = ok p) :
    absPreludeIx p = (⟨#[]⟩ : PreludeIx) := by
  rw [frontend.prepare.prelude_ix_empty] at h
  cases Result.ok_injective h
  rfl

-- `i_declaration_dup_abs` is `Refine2/Dup.lean`'s (task #97-P5-Front round 2:
-- the `arena::env` copies moved down from `Inductives/Shape.lean`).


/-- **`arena::env::i_declaration_names` is `IDeclaration.names`.**  The
`indDecl` arm is `Refine2/Checker/Axioms.lean`'s `block_names_refines`, above
this tier for the same reason. -/
theorem i_declaration_names_abs {d : arena.env.IDeclaration} {v}
    (h : arena.env.i_declaration_names d = ok v) :
    v.val.map absNIdx = (absIDeclaration d).names := by
  have one : ∀ {cv : arena.env.IConstantVal} {v},
      arena.env.i_declaration_one_name cv = ok v → v.val.map absNIdx = [absNIdx cv.name] := by
    intro cv v h
    rw [arena.env.i_declaration_one_name] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ConRon.Refine.vec_push_val h, dupId_nidx _ _ hn]
    simp [alloc.vec.Vec.with_capacity]
  have from_ : ∀ (block : alloc.vec.Vec arena.env.IConstantInfo) (k : Nat) (i : Std.Usize)
      (out v : alloc.vec.Vec arena.handle.NIdx),
      block.val.length - i.val = k →
      arena.env.i_constant_info_names_from block i out = ok v →
      v.val.map absNIdx = out.val.map absNIdx ++
        (block.val.drop i.val).map (fun c => (absIConstantInfo c).name) := by
    intro block k
    induction k with
    | zero =>
      intro i out v hk h
      rw [arena.env.i_constant_info_names_from] at h
      rw [if_pos (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]; simp
    | succ k ih =>
      intro i out v hk h
      rw [arena.env.i_constant_info_names_from] at h
      rw [if_neg (by scalar_tac)] at h
      obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v := usize_add_one_inv hi2
      rw [ih i2 out1 v (by omega) h, ConRon.Refine.vec_push_val ho1, hi2v]
      obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hc)
      rw [List.drop_eq_getElem_cons (l := block.val) hlt, hx]
      simp [i_constant_info_name_abs hn]
  rw [arena.env.i_declaration_names.eq_def] at h
  cases d <;> simp only at h
  all_goals first
    | (rw [one h]; rfl)
    | (cases Result.ok_injective h; rfl)
    | skip
  rename_i block np
  rw [from_ block _ 0#usize _ v rfl h]
  simp [absIDeclaration, IDeclaration.names]

/-- **`prepare::prelude_key` refines `preludeKey`**
(`Arena/Frontend/Prepare.lean:56-59`).  The one reason this takes the store is
con-leche's `.anonymous` fall-through, which over handles is an intern — and
the intern is `Specs.lean`'s `intern_n_node_run` at the lifted state. -/
theorem prelude_key_refines {pers rst lst d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prelude_key pers rst.store d = ok o) :
    Sim₀ absNIdx pers lst (o.1, withStore rst o.2)
      (preludeKey (absIDeclaration d)) := by
  rw [frontend.prepare.prelude_key] at h
  obtain ⟨ns, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hn := i_declaration_names_abs hns
  simp only at h
  split_ifs at h with h0
  · have hnil : (absIDeclaration d).names = [] := by
      rw [← hn]; have : ns.val.length = 0 := by scalar_tac
      simp [List.length_eq_zero_iff.mp this]
    have hrun : arena.monad.intern_n_node pers rst .Anonymous =
        ok (o.1, withStore rst o.2) := by
      rw [arena.monad.intern_n_node, h]; cases o; simp
    have H := intern_n_node_run₀ hrel hinv .Anonymous trivial hrun
    simp only [preludeKey, hnil, List.head?_nil]
    exact H
  · obtain ⟨n, hnn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have e1 := dupId_nidx _ _ hn1
    obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hnn)
    have hhead : (absIDeclaration d).names.head? = some (absNIdx n) := by
      rw [← hn]
      rcases hns' : ns.val with _ | ⟨x, xs⟩
      · simp [hns'] at hlt
      · have h0' : (0#usize : Std.Usize).val = 0 := rfl
        simp only [hns', h0', List.getElem_cons_zero] at hx
        simp [hns', hx]
    simp only [preludeKey, hhead]
    exact ⟨lst, by rw [e1]; rfl, hrel, hinv⟩

/-- **`prepare::declares` refines `declares`**
(`Arena/Frontend/Prepare.lean:74-75`).  Pure on both sides: over handles
`IDeclaration.names` is pure, which is what keeps `findIdx`'s predicate a
predicate (`Arena/Env.lean`'s `tableName` note). -/
theorem declares_refines {n d v} (h : frontend.prepare.declares n d = ok v) :
    v = declares (absNIdx n) (absIDeclaration d) := by
  rw [frontend.prepare.declares] at h
  obtain ⟨ns, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [declares, ← i_declaration_names_abs hns]
  rw [arena.env.nidx_vec_contains] at h
  have key : ∀ (k : Nat) (i : Std.Usize) (o : Bool), ns.val.length - i.val = k →
      arena.env.nidx_vec_contains_from ns i n = ok o →
      o = ((ns.val.drop i.val).map absNIdx).contains (absNIdx n) := by
    intro k
    induction k with
    | zero =>
      intro i o hk h
      rw [arena.env.nidx_vec_contains_from] at h
      rw [if_pos (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]; rfl
    | succ k ih =>
      intro i o hk h
      rw [arena.env.nidx_vec_contains_from] at h
      rw [if_neg (by scalar_tac)] at h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
      obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn1)
      rw [List.drop_eq_getElem_cons hlt, hx, List.map_cons, List.contains_cons]
      cases hbb : b
      · rw [hbb] at h hbv
        rw [if_neg (by simp)] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [ih i2 o (by have := usize_add_one_inv hi2; omega) h,
          usize_add_one_inv hi2]
        have : (absNIdx n == absNIdx n1) = false := by
          rw [BEq.comm]; exact hbv.symm
        simp [this]
      · rw [hbb] at h hbv
        rw [if_pos (by simp), Result.ok.injEq] at h
        subst h
        have : (absNIdx n == absNIdx n1) = true := by
          rw [BEq.comm]; exact hbv.symm
        simp [this]
  rw [key _ 0#usize v rfl h]
  simp

/-- **`prepare::pick_idx`** against this file's transcription. -/
theorem pick_idx_refines {n ds picked k}
    (h : frontend.prepare.pick_idx n ds picked = ok k) :
    k.val = pickIdx (absNIdx n) (absIDeclArr ds) picked.val := by
  -- once a hit is recorded the loop only returns it
  have found : ∀ (k' : Nat) (i hit r : Std.Usize), ds.val.length - i.val = k' →
      hit ≠ alloc.vec.Vec.len ds →
      frontend.prepare.pick_idx_loop n ds picked (alloc.vec.Vec.len ds) i hit = ok r →
      r = hit := by
    intro k' i hit r _ hne h
    rw [frontend.prepare.pick_idx_loop] at h
    split at h <;> exact (Result.ok_injective h).symm
  have key : ∀ (k' : Nat) (i r : Std.Usize), ds.val.length - i.val = k' →
      i.val ≤ ds.val.length →
      frontend.prepare.pick_idx_loop n ds picked (alloc.vec.Vec.len ds) i
        (alloc.vec.Vec.len ds) = ok r →
      r.val = i.val + pickL (declares (absNIdx n))
        ((ds.val.map absIDeclaration).drop i.val) (picked.val.drop i.val) := by
    intro k'
    induction k' with
    | zero =>
      intro i r hk hle h
      rw [frontend.prepare.pick_idx_loop] at h
      rw [if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by simp only [List.length_map]; omega)]
      simp [pickL]; scalar_tac
    | succ k' ih =>
      intro i r hk hle h
      rw [frontend.prepare.pick_idx_loop] at h
      rw [if_pos (by scalar_tac), if_pos rfl] at h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hit1, hh1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v := usize_add_one_inv hi1
      obtain ⟨hbl, hbx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hb)
      have hlt : i.val < ds.val.length := by omega
      have hA : (ds.val.map absIDeclaration).drop i.val =
          absIDeclaration ds.val[i.val] :: (ds.val.map absIDeclaration).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp only [List.length_map]; exact hlt)]
        simp
      have hB : picked.val.drop i.val = b :: picked.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hbl, hbx]
      rw [hA, hB]
      simp only [pickL, List.headD_cons, List.tail_cons]
      split at hh1
      · rename_i hbt
        cases Result.ok_injective hh1
        rw [ih i1 r (by omega) (by omega) h, hi1v]
        simp [hbt]; omega
      · rename_i hbf
        obtain ⟨d, hd, hh1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hh1
        obtain ⟨b1, hb1, hh1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hh1
        obtain ⟨_, hdx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hd)
        have hdecl := declares_refines hb1
        rw [← hdx] at hdecl
        split at hh1
        · rename_i hb1t
          cases Result.ok_injective hh1
          have := found _ i1 i r rfl (by scalar_tac) h
          subst this
          simp [hbf, ← hdecl, hb1t]
        · rename_i hb1f
          cases Result.ok_injective hh1
          rw [ih i1 r (by omega) (by omega) h, hi1v]
          simp [hbf, ← hdecl, hb1f]; omega
  rw [frontend.prepare.pick_idx] at h
  have := key _ 0#usize k rfl (by simp) h
  simpa [pickIdx, absIDeclArr] using this

/-- **`prepare::no_picks`** — `n` falses. -/
theorem no_picks_refines {n v} (h : frontend.prepare.no_picks n = ok v) :
    v.val = List.replicate n.val false := by
  have key : ∀ (k : Nat) (i : Std.Usize) (p : alloc.vec.Vec Bool) (v : alloc.vec.Vec Bool),
      n.val - i.val = k →
      frontend.prepare.no_picks_loop n p i = ok v →
      v.val = p.val ++ List.replicate (n.val - i.val) false := by
    intro k
    induction k with
    | zero =>
      intro i p v hk h
      rw [frontend.prepare.no_picks_loop] at h
      rw [if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [hk]; simp
    | succ k ih =>
      intro i p v hk h
      rw [frontend.prepare.no_picks_loop] at h
      rw [if_pos (by scalar_tac)] at h
      obtain ⟨p1, hp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v := usize_add_one_inv hi1
      rw [ih i1 p1 v (by omega) h, ConRon.Refine.vec_push_val hp1,
        show n.val - i.val = (n.val - i1.val) + 1 by omega, List.replicate_succ]
      simp
  rw [frontend.prepare.no_picks] at h
  rw [key _ 0#usize _ v rfl h]
  simp [alloc.vec.Vec.with_capacity]

/-- The plan's abstraction: the front and the rest it stands for. -/
def absPlan (ps ds : alloc.vec.Vec arena.env.IDeclaration)
    (p : alloc.vec.Vec Std.Usize × alloc.vec.Vec Bool) :
    Array IDeclaration × Array IDeclaration :=
  (preparedFront (absIDeclArr ps) (absIDeclArr ds) (p.1.val.map (·.val)),
   preparedRest (absIDeclArr ds) p.2.val)

/-- What the plan's consumers need of its shape: a slot per prelude record and
a mask bit per stream record. -/
def PlanWF (ps ds : alloc.vec.Vec arena.env.IDeclaration)
    (p : alloc.vec.Vec Std.Usize × alloc.vec.Vec Bool) : Prop :=
  p.1.val.length = ps.val.length ∧ p.2.val.length = ds.val.length

/-- `front_of`'s outcome relation: the plan stands for the twin's front and
rest, and has the shape its consumers need (`SimRel₀`'s way of carrying a
representation predicate on the Rust result). -/
def PlanRel (ps ds : alloc.vec.Vec arena.env.IDeclaration)
    (p : alloc.vec.Vec Std.Usize × alloc.vec.Vec Bool)
    (v : Array IDeclaration × Array IDeclaration) : Prop :=
  v = absPlan ps ds p ∧ PlanWF ps ds p

theorem vec_index_mut_set {v w : alloc.vec.Vec Bool} {k : Std.Usize}
    (h : (do
      let (_, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Bool) v k
      ok (back true)) = ok w) :
    w.val = v.val.set k.val true := by
  obtain ⟨⟨x, back⟩, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [alloc.vec.Vec.index_mut,
    core.slice.index.Usize.index_mut, Slice.index_mut_usize] at hb
  obtain ⟨p, hp, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  obtain ⟨y, hy, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  cases Result.ok_injective hp
  cases Result.ok_injective hb
  cases Result.ok_injective h
  show (Slice.from _ _).val = _
  rw [Slice.from_val]; rfl

/-- **`prepare::front_of`'s loop** against `frontOf`, from prelude slot `j`:
the twin's accumulator is the front the plan so far stands for, and the
twin's remaining stream is the records the mask does not carry. -/
theorem front_of_loop_refines {pers ps ds} :
    ∀ (j : Std.Usize) (picked : alloc.vec.Vec Bool) (picks : alloc.vec.Vec Std.Usize)
      (rst : arena.monad.AState) (lst : AState) (o),
      AStateRel₀ pers rst lst → AStateInv pers rst →
      picked.val.length = ds.val.length → picks.val.length = j.val →
      j.val ≤ ps.val.length →
      frontend.prepare.front_of_loop pers rst.store ps ds (alloc.vec.Vec.len ds)
        picked (alloc.vec.Vec.len ps) picks j = ok o →
      SimRel₀ (PlanRel ps ds) pers lst (o.1, withStore rst o.2)
        (frontOf (preparedFront (absIDeclArr ps) (absIDeclArr ds) (picks.val.map (·.val)))
          ((absIDeclArr ps).toList.drop j.val)
          (preparedRest (absIDeclArr ds) picked.val)) := by
  suffices H : ∀ (k : Nat) (j : Std.Usize) (picked : alloc.vec.Vec Bool)
      (picks : alloc.vec.Vec Std.Usize) (rst : arena.monad.AState) (lst : AState) (o),
      ps.val.length - j.val = k →
      AStateRel₀ pers rst lst → AStateInv pers rst →
      picked.val.length = ds.val.length → picks.val.length = j.val →
      j.val ≤ ps.val.length →
      frontend.prepare.front_of_loop pers rst.store ps ds (alloc.vec.Vec.len ds)
        picked (alloc.vec.Vec.len ps) picks j = ok o →
      SimRel₀ (PlanRel ps ds) pers lst (o.1, withStore rst o.2)
        (frontOf (preparedFront (absIDeclArr ps) (absIDeclArr ds) (picks.val.map (·.val)))
          ((absIDeclArr ps).toList.drop j.val)
          (preparedRest (absIDeclArr ds) picked.val)) from
    fun j picked picks rst lst o => H _ j picked picks rst lst o rfl
  intro k
  induction k with
  | zero =>
    intro j picked picks rst lst o hk hrel hinv hpl hpk hj h
    rw [frontend.prepare.front_of_loop] at h
    rw [if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    have hnil : (absIDeclArr ps).toList.drop j.val = [] := by
      simp only [absIDeclArr, List.toList_toArray, List.drop_eq_nil_iff, List.length_map]
      omega
    rw [hnil]
    exact ⟨_, lst, rfl, ⟨rfl, by show picks.val.length = ps.val.length; omega, hpl⟩,
      hrel, hinv⟩
  | succ k ih =>
    intro j picked picks rst lst o hk hrel hinv hpl hpk hj h
    rw [frontend.prepare.front_of_loop] at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨d, hdv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1⟩, hkey, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hK := prelude_key_refines hrel hinv hkey
    have hdi := vec_index_some hdv
    have hcons : (absIDeclArr ps).toList.drop j.val =
        absIDeclaration d :: (absIDeclArr ps).toList.drop (j.val + 1) := by
      simp only [absIDeclArr, List.toList_toArray]
      rw [List.drop_eq_getElem_cons (by simp only [List.length_map]; omega)]
      simp only [List.getElem_map]
      obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.mp hdi
      rw [hx]
    rw [hcons]
    simp only [Sim₀] at hK
    simp only [SimRel₀]
    simp only [frontOf, am_run_bind']
    cases r with
    | Err e =>
      have ho := Result.ok_injective h; subst ho
      exact AErrSim.bind hK _
    | Ok v =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hK
      rw [hx1]
      simp only [except_ok_bind]
      obtain ⟨kk, hkk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hkv := pick_idx_refines hkk
      obtain ⟨picked1, hp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hp1v : picked1.val = picked.val.set kk.val true := by
        split at hp1
        · exact vec_index_mut_set hp1
        · cases Result.ok_injective hp1
          rw [List.set_eq_of_length_le (by scalar_tac)]
      obtain ⟨picks1, hpk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hpk1v := ConRon.Refine.vec_push_val hpk1
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj1v := usize_add_one_inv hj1
      have hpick := pick_preparedRest (absNIdx v) (absIDeclArr ds) picked.val
        (by simp [absIDeclArr, hpl])
      rw [← hkv] at hpick
      rw [hpick]
      have hR := ih j1 picked1 picks1 (withStore rst ar1) lst1 o (by omega) hrel1 hinv1
        (by rw [hp1v]; simp [hpl]) (by rw [hpk1v]; simp [hpk, hj1v]) (by omega) h
      have hF : (preparedFront (absIDeclArr ps) (absIDeclArr ds)
            (picks.val.map (·.val))).push
            (((absIDeclArr ds)[kk.val]?).getD (absIDeclaration d)) =
          preparedFront (absIDeclArr ps) (absIDeclArr ds) (picks1.val.map (·.val)) := by
        rw [hpk1v, List.map_append, List.map_cons, List.map_nil, preparedFront_push]
        congr 2
        simp only [List.length_map, hpk, absIDeclArr]
        simp [hdi]
      rw [hF, ← hp1v, show j.val + 1 = j1.val by omega]
      exact hR

/-- **`prepare::front_of` refines `frontOf`** — the plan and the mask, which
stand for the twin's front and rest (`absPlan`). -/
theorem front_of_refines {pers rst lst ps ds o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.front_of pers rst.store ps ds = ok o) :
    SimRel₀ (PlanRel ps ds) pers lst (o.1, withStore rst o.2)
      (frontOf #[] (absIDeclArr ps).toList (absIDeclArr ds)) := by
  rw [frontend.prepare.front_of] at h
  obtain ⟨picked, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hpv := no_picks_refines hp
  have H := front_of_loop_refines 0#usize picked
    (alloc.vec.Vec.with_capacity Std.Usize (alloc.vec.Vec.len ps)) rst lst o hrel hinv
    (by rw [hpv]; simp) (by simp) (by simp) h
  have hfront : preparedFront (absIDeclArr ps) (absIDeclArr ds)
      ((alloc.vec.Vec.with_capacity Std.Usize (alloc.vec.Vec.len ps)).val.map (·.val))
      = #[] := by
    simp [preparedFront, frontL, alloc.vec.Vec.with_capacity]
  have hrest : preparedRest (absIDeclArr ds) picked.val = absIDeclArr ds := by
    rw [hpv]
    simp only [preparedRest, absIDeclArr, List.toList_toArray]
    rw [restL_none _ _ (by simp)]
  rw [hfront, hrest] at H
  simpa using H

/-- **`prepare::prepared_front`** against the transcription.  The plan has a
slot per prelude record (`hlen`), which is what `front_of` hands it. -/
theorem prepared_front_refines {out ps ds picks v}
    (hlen : picks.val.length = ps.val.length)
    (h : frontend.prepare.prepared_front out ps ds picks = ok v) :
    absIDeclArr v = absIDeclArr out ++
      preparedFront (absIDeclArr ps) (absIDeclArr ds) (picks.val.map (·.val)) := by
  have key : ∀ (k : Nat) (j : Std.Usize) (out v : alloc.vec.Vec arena.env.IDeclaration),
      ps.val.length - j.val = k →
      frontend.prepare.prepared_front_loop ps ds picks out (alloc.vec.Vec.len ds)
        (alloc.vec.Vec.len ps) j = ok v →
      v.val.map absIDeclaration = out.val.map absIDeclaration ++
        frontL (absIDeclArr ps) (absIDeclArr ds) ((picks.val.map (·.val)).drop j.val) j.val := by
    intro k
    induction k with
    | zero =>
      intro j out v hk h
      rw [frontend.prepare.prepared_front_loop] at h
      rw [if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      have : (picks.val.map (·.val)).drop j.val = [] := by
        simp only [List.drop_eq_nil_iff, List.length_map]; omega
      rw [this]; simp [frontL]
    | succ k ih =>
      intro j out v hk h
      rw [frontend.prepare.prepared_front_loop] at h
      rw [if_pos (by scalar_tac)] at h
      obtain ⟨kk, hkk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hkki := vec_index_some hkk
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj1v := usize_add_one_inv hj1
      have hcons : (picks.val.map (·.val)).drop j.val =
          kk.val :: (picks.val.map (·.val)).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by
          simp only [List.length_map]; exact (List.getElem?_eq_some_iff.mp hkki).1)]
        simp only [List.getElem_map]
        obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.mp hkki
        rw [hx]
      rw [ih j1 out1 v (by omega) h, hcons, frontL, ← hj1v]
      have hstep : out1.val.map absIDeclaration = out.val.map absIDeclaration ++
          [(absIDeclArr ds)[kk.val]?.getD ((absIDeclArr ps).getD j.val default)] := by
        split at hout1
        · rename_i hlt
          obtain ⟨d, hd, hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
          obtain ⟨d', hd', hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
          rw [ConRon.Refine.vec_push_val hout1]
          have hdi := vec_index_some hd
          simp [absIDeclArr, hdi, i_declaration_dup_abs hd']
        · rename_i hge
          obtain ⟨d, hd, hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
          obtain ⟨d', hd', hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
          rw [ConRon.Refine.vec_push_val hout1]
          have hdi := vec_index_some hd
          have hnone : ds.val[kk.val]? = none := List.getElem?_eq_none (by scalar_tac)
          simp [absIDeclArr, hdi, hnone, i_declaration_dup_abs hd']
      rw [hstep]; simp
  rw [frontend.prepare.prepared_front] at h
  have := key _ 0#usize out v rfl h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  simp only [absIDeclArr, this, h0, List.drop_zero, preparedFront]
  simp

/-- **`prepare::prepared_rest`** against the transcription. -/
theorem prepared_rest_refines {out ds picked v}
    (h : frontend.prepare.prepared_rest out ds picked = ok v) :
    absIDeclArr v = absIDeclArr out ++ preparedRest (absIDeclArr ds) picked.val := by
  have key : ∀ (k : Nat) (i : Std.Usize) (out v : alloc.vec.Vec arena.env.IDeclaration),
      ds.val.length - i.val = k →
      frontend.prepare.prepared_rest_loop ds picked out (alloc.vec.Vec.len ds) i = ok v →
      v.val.map absIDeclaration = out.val.map absIDeclaration ++
        restL ((ds.val.map absIDeclaration).drop i.val) (picked.val.drop i.val) := by
    intro k
    induction k with
    | zero =>
      intro i out v hk h
      rw [frontend.prepare.prepared_rest_loop] at h
      rw [if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      have : (ds.val.map absIDeclaration).drop i.val = [] := by
        simp only [List.drop_eq_nil_iff, List.length_map]; omega
      rw [this]; simp [restL]
    | succ k ih =>
      intro i out v hk h
      rw [frontend.prepare.prepared_rest_loop] at h
      rw [if_pos (by scalar_tac)] at h
      obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbbi := vec_index_some hbb
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v := usize_add_one_inv hi1
      rw [ih i1 out1 v (by omega) h, hi1v]
      have hlt : i.val < ds.val.length := by omega
      obtain ⟨hbl, hbx⟩ := List.getElem?_eq_some_iff.mp hbbi
      have hA : (ds.val.map absIDeclaration).drop i.val =
          absIDeclaration ds.val[i.val] :: (ds.val.map absIDeclaration).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp only [List.length_map]; exact hlt)]
        simp
      have hB : picked.val.drop i.val = bb :: picked.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hbl, hbx]
      rw [hA, hB]
      simp only [restL, List.headD_cons, List.tail_cons]
      split at hout1
      · rename_i hb
        cases Result.ok_injective hout1
        simp [hb]
      · rename_i hb
        obtain ⟨d, hd, hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
        obtain ⟨d', hd', hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
        rw [ConRon.Refine.vec_push_val hout1]
        have hdi := vec_index_some hd
        obtain ⟨_, hdx⟩ := List.getElem?_eq_some_iff.mp hdi
        simp [hb, i_declaration_dup_abs hd', hdx]
  rw [frontend.prepare.prepared_rest] at h
  have := key _ 0#usize out v rfl h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  simp only [absIDeclArr, preparedRest, this, h0, List.drop_zero, List.toList_toArray]
  simp

/-- **`prepare::prepared_stream`** against the transcription. -/
theorem prepared_stream_refines {ps ds picks picked v}
    (hlen : picks.val.length = ps.val.length)
    (h : frontend.prepare.prepared_stream ps ds picks picked = ok v) :
    absIDeclArr v = preparedStream (absIDeclArr ps) (absIDeclArr ds)
      (picks.val.map (·.val)) picked.val := by
  rw [frontend.prepare.prepared_stream] at h
  obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [prepared_rest_refines h, prepared_front_refines hlen hv1]
  simp [preparedStream, alloc.vec.Vec.with_capacity]

end ConRon.Refine2.Frontend

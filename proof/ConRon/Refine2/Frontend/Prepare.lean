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

The answer is `Refine2/Checker/Spec.lean`'s pattern at this tier's scale: a
twin-side transcription of what the plan MEANS (`pickIdx`, `preparedFront`,
`preparedRest`, `preparedStream`) with one `_unfold` equation tying the
composite back to the twin's `frontOf`, so that a reader checks the
transcription against `Arena/Frontend/Prepare.lean` clause for clause rather
than reading it out of a proof.  The equation is `preparedStream_eq_frontOf`
and it is this file's one real obligation; everything else above it follows.

**That equation is the port's own correctness argument, not a representation
one**, which is why it is stated and not assumed: the port is right only
because a masked record is exactly an erased one, and `RefineOld/Frontend/
PrepareR.lean` is where the `Expr`-tree port's version of it was proved
(1 904 lines, `front_of_refines`).  Over handles the argument is the same; the
proof is not transcribed here, for the reason DESIGN.md's section gives.

## `sorry` count in this file: 12
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

/-- **`arena::env::i_declaration_dup` is the identity under the abstraction.**
`Refine2/Inductives/Shape.lean`'s `i_constant_info_dup_abs` family is the
proof's substance; that file is above this tier (it imports the Core knot), so
the lemma is restated here until the family moves down. -/
theorem i_declaration_dup_abs {d o : arena.env.IDeclaration}
    (h : arena.env.i_declaration_dup d = ok o) :
    absIDeclaration o = absIDeclaration d := by sorry

/-- **`arena::env::i_declaration_names` is `IDeclaration.names`.**  The
`indDecl` arm is `Refine2/Checker/Axioms.lean`'s `block_names_refines`, above
this tier for the same reason. -/
theorem i_declaration_names_abs {d : arena.env.IDeclaration} {v}
    (h : arena.env.i_declaration_names d = ok v) :
    v.val.map absNIdx = (absIDeclaration d).names := by sorry

/-- **`prepare::prelude_key` refines `preludeKey`**
(`Arena/Frontend/Prepare.lean:56-59`).  The one reason this takes the store is
con-leche's `.anonymous` fall-through, which over handles is an intern.

**Open on the `M_FROZEN` ruling** (task #97-P5-Front): at a frozen name tier
(`shared_on` and not `scratch_on`) the port's intern answers
`Internal (M_FROZEN)` where the twin appends, so the error arm is false there
until the frozen guard turns `Native` (the pending Rust commit).  Under
`estore_intern_name_abs`'s `hfrozen` the arm closes; the success arm holds
either way. -/
theorem prelude_key_refines {pers rst lst d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prelude_key pers rst.store d = ok o) :
    Sim absNIdx (fun _ => True) pers lst (o.1, withStore rst o.2)
      (preludeKey (absIDeclaration d)) := by sorry

/-- **`prepare::declares` refines `declares`**
(`Arena/Frontend/Prepare.lean:74-75`).  Pure on both sides: over handles
`IDeclaration.names` is pure, which is what keeps `findIdx`'s predicate a
predicate (`Arena/Env.lean`'s `tableName` note). -/
theorem declares_refines {n d v} (h : frontend.prepare.declares n d = ok v) :
    v = declares (absNIdx n) (absIDeclaration d) := by sorry

/-- **`prepare::pick_idx`** against this file's transcription. -/
theorem pick_idx_refines {n ds picked k}
    (h : frontend.prepare.pick_idx n ds picked = ok k) :
    k.val = pickIdx (absNIdx n) (absIDeclArr ds) picked.val := by sorry

/-- **`prepare::no_picks`** — `n` falses. -/
theorem no_picks_refines {n v} (h : frontend.prepare.no_picks n = ok v) :
    v.val = List.replicate n.val false := by sorry

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

/-- **`prepare::front_of`'s loop** against `frontOf`, from prelude slot `j`:
the twin's accumulator is the front the plan so far stands for, and the
twin's remaining stream is the records the mask does not carry. -/
theorem front_of_loop_refines {pers ps ds} :
    ∀ (j : Std.Usize) (picked : alloc.vec.Vec Bool) (picks : alloc.vec.Vec Std.Usize)
      (rst : arena.monad.AState) (lst : AState) (o),
      AStateRel pers rst lst → AStateInv pers rst →
      picked.val.length = ds.val.length → picks.val.length = j.val →
      frontend.prepare.front_of_loop pers rst.store ps ds (alloc.vec.Vec.len ds)
        picked (alloc.vec.Vec.len ps) picks j = ok o →
      Sim (absPlan ps ds) (PlanWF ps ds) pers lst (o.1, withStore rst o.2)
        (frontOf (preparedFront (absIDeclArr ps) (absIDeclArr ds) (picks.val.map (·.val)))
          ((absIDeclArr ps).toList.drop j.val)
          (preparedRest (absIDeclArr ds) picked.val)) := by sorry

/-- **`prepare::front_of` refines `frontOf`** — the plan and the mask, which
stand for the twin's front and rest (`absPlan`). -/
theorem front_of_refines {pers rst lst ps ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.front_of pers rst.store ps ds = ok o) :
    Sim (absPlan ps ds) (PlanWF ps ds) pers lst (o.1, withStore rst o.2)
      (frontOf #[] (absIDeclArr ps).toList (absIDeclArr ds)) := by
  rw [frontend.prepare.front_of] at h
  obtain ⟨picked, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hpv := no_picks_refines hp
  have H := front_of_loop_refines 0#usize picked
    (alloc.vec.Vec.with_capacity Std.Usize (alloc.vec.Vec.len ps)) rst lst o hrel hinv
    (by rw [hpv]; simp) (by simp) h
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
  sorry

/-- **`prepare::prepared_rest`** against the transcription. -/
theorem prepared_rest_refines {out ds picked v}
    (h : frontend.prepare.prepared_rest out ds picked = ok v) :
    absIDeclArr v = absIDeclArr out ++ preparedRest (absIDeclArr ds) picked.val := by
  sorry

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

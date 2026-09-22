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

Four definitions and one equation.  Read them against
`Arena/Frontend/Prepare.lean:77-101` (`pick`, `frontOf`). -/

/-- The twin-side reading of `prepare::pick_idx`: the index of the first
record of `ds` that is not masked and declares `n`, or `ds.length`. -/
def pickIdx (n : NIdx) (ds : Array IDeclaration) (picked : List Bool) : Nat :=
  let rec go (i : Nat) : Nat :=
    if h : i < ds.size then
      if picked.getD i false = false && declares n ds[i] then i
      else go (i + 1)
    else ds.size
  termination_by ds.size - i
  decreasing_by omega
  go 0

/-- The twin-side reading of `prepare::prepared_front`: slot `j` is the
stream's own copy where the plan found one, the prelude's own where it did
not. -/
def preparedFront (ps ds : Array IDeclaration) (picks : List Nat) :
    Array IDeclaration :=
  (picks.zipIdx.map fun (k, j) =>
    if h : k < ds.size then ds[k] else ps.getD j default).toArray

/-- The twin-side reading of `prepare::prepared_rest`: the stream's records
the mask does not carry, in the stream's order. -/
def preparedRest (ds : Array IDeclaration) (picked : List Bool) :
    Array IDeclaration :=
  (ds.toList.zipIdx.filterMap fun (d, i) =>
    if picked.getD i false then none else some d).toArray

/-- The twin-side reading of `prepare::prepared_stream`. -/
def preparedStream (ps ds : Array IDeclaration) (picks : List Nat)
    (picked : List Bool) : Array IDeclaration :=
  preparedFront ps ds picks ++ preparedRest ds picked

/-- **The file's one real obligation**: the port's plan-and-mask is the
twin's erase-and-recurse.  `RefineOld/Frontend/PrepareR.lean`'s
`front_of_refines` is this statement for the `Expr`-tree port. -/
theorem preparedStream_eq_frontOf {ps ds : Array IDeclaration}
    {picks : List Nat} {picked : List Bool} {acc : Array IDeclaration}
    {lst : AState} {out : Array IDeclaration × Array IDeclaration} {lst' : AState}
    (h : (frontOf acc ps.toList ds).run lst = .ok (out, lst')) :
    preparedStream ps ds picks picked = acc ++ out.1 ++ out.2 := by
  sorry

/-! ## The eleven functions -/

/-- **`prepare::prelude_ix_empty`** — the empty prelude, the twin's field
default. -/
theorem prelude_ix_empty_refines {p : frontend.prepare.PreludeIx}
    (h : frontend.prepare.prelude_ix_empty = ok p) :
    absPreludeIx p = (⟨#[]⟩ : PreludeIx) := by sorry

/-- **`prepare::prelude_key` refines `preludeKey`**
(`Arena/Frontend/Prepare.lean:56-59`).  The one reason this takes the store is
con-leche's `.anonymous` fall-through, which over handles is an intern. -/
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

/-- **`prepare::front_of`** — the plan and the mask. -/
theorem front_of_refines {pers rst lst ps ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.front_of pers rst.store ps ds = ok o) :
    ∀ picks picked, o.1 = .Ok (picks, picked) →
      ∃ lst' out, (frontOf #[] (absIDeclArr ps).toList (absIDeclArr ds)).run lst
          = .ok (out, lst') ∧
        AStateRel pers (withStore rst o.2) lst' ∧
        AStateInv pers (withStore rst o.2) ∧ Ext lst.store lst'.store ∧
        preparedStream (absIDeclArr ps) (absIDeclArr ds)
            (picks.val.map (·.val)) picked.val = out.1 ++ out.2 := by sorry

/-- **`prepare::prepared_front`** against the transcription. -/
theorem prepared_front_refines {out ps ds picks v}
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
    (h : frontend.prepare.prepared_stream ps ds picks picked = ok v) :
    absIDeclArr v = preparedStream (absIDeclArr ps) (absIDeclArr ds)
      (picks.val.map (·.val)) picked.val := by sorry

/-- **`prepare::prepare_d` refines `prepareD`**
(`Arena/Frontend/Prepare.lean:128-131`) — one of the tier's named
deliverables. -/
theorem prepare_d_refines {pers rst lst pre ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prepare_d pers rst pre ds = ok o) :
    Sim absPrepared (fun _ => True) pers lst o
      (prepareD (absPreludeIx pre) (absIDeclArr ds)) := by sorry

/-- **`prepare::prepare_prelude` refines `preparePrelude`**
(`Arena/Frontend/Prepare.lean:138-140`) — the second half of what the driver
runs after the parse, and what `Refine2/Checker/Top.lean`'s
`install_then_check_refines` is handed. -/
theorem prepare_prelude_refines {pers rst lst pre ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prepare_prelude pers rst pre ds = ok o) :
    Sim absIDeclArr (fun _ => True) pers lst o
      (preparePrelude (absPreludeIx pre) (absIDeclArr ds)) := by sorry

end ConRon.Refine2.Frontend

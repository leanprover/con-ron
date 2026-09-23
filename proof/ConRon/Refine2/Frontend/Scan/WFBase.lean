import ConRon.Refine.Abs
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.Env
import ConRon.Refine.Nat

/-! # The parser's well-formedness vocabulary (task #85, phase 1)

`Refine/Main.lean`'s last standing input hypothesis is

    hds : ∀ d ∈ ds.val, DeclarationWF d

— "every declaration handed to the fold is what the port's own smart
constructors built".  Task #73 discharged it with a runtime validation pass and
task #81 withdrew that pass; task #84 put the parser into the verified core, and
this group of files discharges `hds` the way DESIGN.md §3.5 said it would fall
out all along: **by construction**, because `ExprWF`/`NameWF`/`LevelWF`'s
constructors *are* `expr::app`, `name::mk_str`, `level::succ`, … and the parse
reaches every node it stores through exactly one of them.

## What this file fixes

The vocabulary the rest of the group is stated in.

* `MapValsWF P m` — every value a `ron::HashMap` holds satisfies `P`.  Stated
  over `HashMap.al_v` (the recorded entries) rather than `HashMap.toFun`, so
  that `ExprOps.get_mem`/`ExprOps.insert_pres` apply with **no** `Eq2Spec` and
  no `Inv`: for a predicate that ignores the key, `ExprOps.Compat` is trivial.
  That is the whole reason the parse's `Name`-keyed maps cost nothing here
  (`Refine/HashMapWF.lean`'s note explains why `Eq2Spec` is unusable at a key
  type whose equality is the port's own `name::beq`).
* `IdTableWF P t` — the parse's three index tables (`scan_types::IdTable`: a
  dense prefix and a sparse overflow map), every entry of both halves.
* `StateDWF st` — the parse state's invariant, the six fields that hold terms.
  The other eleven are counters, flags, receipts and the three tables the
  *modeller* reads, and nothing that reaches a stored `Declaration` reads them,
  so they carry no clause (see `ModellerWF`).
* `NameRecWF`/`ExprRecWF`/`LineRecWF` — the one thing the *scanner* owes the
  parse: a `Vec<u32>` it produced as a string payload holds valid code points.
  `Refine/Frontend/ScanWF.lean` proves it of `scan_line_fwd`.
* `ProjRecOwnerWF` — the recorded structure owner the projection rewrite reads.
* `ModellerWF` — **the residue**.  The maintainer's ruling (2026-09-13):
  *"leave the modeller unverified if you can; rumors are that upstream can
  actually get rid of it."*  Task #84's seam makes the parse quantify over
  `in_model_rec::Modeller`, so what the proof needs of it is one line: whatever
  `generate` returns is well formed.  It is a hypothesis of the capstones and
  disappears the day upstream drops the modeller.

## `sorry` count in this file: 0

**Task #97-P5-Front**: the scanner-facing half of `RefineOld/Frontend/Base.lean`
(its `StateDWF`/`ModellerWF` half is about the `Expr`-tree port and stays behind).
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine2.Frontend
open ConRon.Refine

/-! ## Values of a `ron::HashMap` -/

/-- Every value the table holds satisfies `P`. -/
def MapValsWF {K V : Type} (P : V → Prop) (m : ron.hashmap.HashMap K V) : Prop :=
  ∀ p ∈ HashMap.al_v m, P p.2

/-- The key-blind reading of `ExprOps.Compat`, which is what lets `get_mem` and
`insert_pres` be used with neither `Eq2Spec` nor `Inv`. -/
theorem compat_of_vals {K V : Type} {Eq2Inst : ron.hashmap.Eq2 K} (P : V → Prop) :
    ExprOps.Compat Eq2Inst (fun (_ : K) (v : V) => P v) :=
  fun _ _ _ _ h _ _ => h

/-- **A hit returns a recorded value.** -/
theorem map_get_wf {K V : Type} {HashableInst : ron.hashmap.Hashable K}
    {Eq2Inst : ron.hashmap.Eq2 K} {P : V → Prop} {m : ron.hashmap.HashMap K V}
    (hm : MapValsWF P m) {k : K} {r : V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok (some r)) : P r := by
  obtain ⟨k', hmem, -⟩ := ExprOps.get_mem h
  exact hm _ hmem

/-- **An insert records its own value and nothing else.** -/
theorem map_insert_wf {K V : Type} {HashableInst : ron.hashmap.Hashable K}
    {Eq2Inst : ron.hashmap.Eq2 K} {P : V → Prop} {m m' : ron.hashmap.HashMap K V}
    {k : K} {v : V} {old : Option V}
    (hm : MapValsWF P m) (hnew : P v)
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    MapValsWF P m' :=
  ExprOps.insert_pres (compat_of_vals P) hm hnew h

/-- A fresh table holds nothing. -/
theorem map_new_wf {K V : Type} {P : V → Prop} {m : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.new K V = ok m) : MapValsWF P m := by
  rw [ron.hashmap.HashMap.new] at h
  intro p hp
  rw [← Result.ok_injective h] at hp
  simp [HashMap.al_v, alloc.vec.Vec.new] at hp

/-! ## The parse's index tables -/

/-- `scan_types::IdTable`: the dense prefix and the sparse overflow map. -/
def IdTableWF {T : Type} (P : T → Prop) (t : frontend.scan_types.IdTable T) : Prop :=
  (∀ x ∈ t.dense.val, P x) ∧ MapValsWF P t.sparse

/-! ## The scanner's one obligation -/

/-- A name record's string payload holds valid code points. -/
def NameRecWF : frontend.scan_types.NameRec → Prop
  | .Str _ s => StrWF s
  | .Num _ _ => True

/-- An expression record's string payload holds valid code points.  The `NatVal`
arm's digits are bytes and carry no clause: `nat_decimal::from_decimal` gives
`ron::nat`'s own normal form for whatever it accepts. -/
def ExprRecWF : frontend.scan_types.ExprRec → Prop
  | .StrVal s => StrWF s
  | _ => True

/-- One scanned line: the two records that carry a string.  A `Decl` record's
`Vec<u32>` fields are the `safety` and `quotKind` *spellings*, which are
compared with literals and never become a `Name`, so they carry no clause. -/
def LineRecWF : frontend.scan_types.LineRec → Prop
  | .Name _ r => NameRecWF r
  | .Expr _ r => ExprRecWF r
  | _ => True


end ConRon.Refine2.Frontend

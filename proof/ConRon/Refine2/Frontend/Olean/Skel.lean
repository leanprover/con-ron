/-
# `ConRon.Refine2.Frontend.Olean.Skel` — the skeletons of `olean/spec.rs`

**Task #142, Theorem 2.**  What holds no handle: `hints_skel`, `rule_skel`, `kind_skel`,
`const_skel`, `import_skel`, `module_skel`, against upstream's own, which the twin imports.

A skeleton's numbers are saturating words (`SatRel`); `skel_fits` turns the saturated one
into the `Native` decline, and from there on they are the `Nat`s (`KindRel` at `Eq`).
A string is one of the few the skeleton spells, so it is `StrWF`.
-/
import ConRon.Refine2.Frontend.Olean.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_fld region_down region_tag region_nobjs region_fits
  region_list region_nat_sat region_ptr_fld region_bool region_u8 region_u32 region_is_ctor
  region_obj_array region_loc)
open frontend.olean.spec (nat_f name_list hints_skel rule_skel rules_skel kind_skel kind_skel_defn
  kind_skel_induct kind_skel_recur const_skel import_skel imports_skel module_skel)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel)
open ConRon.Refine (StrWF)

/-- A number of a skeleton, as `Nat`: `RN` says how, `SatRel` or the plain value. -/
abbrev NatRel := Std.U64 → Nat → Prop

/-- Its value, once `skel_fits` has passed. -/
@[reducible] def ValRel : NatRel := fun k n => k.val = n

/-- A list, elementwise. -/
@[reducible] def ListA {α β : Type} (A : α → β) (v : alloc.vec.Vec α) (l : List β) : Prop :=
  v.val.map A = l

/-- A recursor rule. -/
def RuleRel {N N' E E' : Type} (AN : N → N') (AE : E → E') (RN : NatRel)
    (r : N × Std.U64 × E) (r' : N' × Nat × E') : Prop :=
  AN r.1 = r'.1 ∧ RN r.2.1 r'.2.1 ∧ AE r.2.2 = r'.2.2

/-- **`spec::CKindF` against upstream's**, generic in what stands for a name and an
expression, and in how a number is read. -/
def KindRel {N N' E E' : Type} (AN : N → N') (AE : E → E') (RN : NatRel) :
    frontend.olean.spec.CKindF N E → CKindF N' E' → Prop
  | .Ax u, .ax u' => u = u'
  | .Defn v h s, .defn v' h' s' =>
      AE v = v' ∧ absHintsRec h = h' ∧ ConRon.Refine.absString s = s' ∧ StrWF s
  | .Thm v all, .thm v' all' => AE v = v' ∧ ListA AN all all'
  | .Opaq v u, .opaq v' u' => AE v = v' ∧ u = u'
  | .Quot k, .quot k' => ConRon.Refine.absString k = k' ∧ StrWF k
  | .Induct np ni all cs nn ir iu irf, .induct np' ni' all' cs' nn' ir' iu' irf' =>
      RN np np' ∧ RN ni ni' ∧ ListA AN all all' ∧ ListA AN cs cs' ∧ RN nn nn' ∧
        ir = ir' ∧ iu = iu' ∧ irf = irf'
  | .Ctor ind ci np nf iu, .ctor ind' ci' np' nf' iu' =>
      AN ind = ind' ∧ RN ci ci' ∧ RN np np' ∧ RN nf nf' ∧ iu = iu'
  | .Recur all np ni nmo nmi rules k iu, .recur all' np' ni' nmo' nmi' rules' k' iu' =>
      ListA AN all all' ∧ RN np np' ∧ RN ni ni' ∧ RN nmo nmo' ∧ RN nmi nmi' ∧
        List.Forall₂ (RuleRel AN AE RN) rules.val rules' ∧ k = k' ∧ iu = iu'
  | _, _ => False

/-- **`spec::CEntryF` against upstream's.** -/
structure EntryRel {N N' E E' : Type} (AN : N → N') (AE : E → E') (RN : NatRel)
    (c : frontend.olean.spec.CEntryF N E) (c' : CEntryF N' E') : Prop where
  «name» : AN c.name = c'.name
  levelParams : ListA AN c.level_params c'.levelParams
  type : AE c.ty = c'.type
  kind : KindRel AN AE RN c.kind c'.kind

/-- A skeleton, against upstream's. -/
abbrev SkelRel := EntryRel absWord absWord SatRel

/-- An `Option` of a skeleton read: `Rel`, with the answers as a relation. -/
abbrev OptRel {α β : Type} (R : α → β → Prop) := Option.Rel R

end ConRon.Refine2.Frontend.Olean

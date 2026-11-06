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
open ConRon.Refine.HashMap (uscalar_add_eq)

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

/-! ## Reading a field -/

open ConLeche.Frontend.Olean in
/-- **`nat_f` is `Region.natF`.** -/
theorem nat_f_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : nat_f bs r g i = ok o) : Option.Rel SatRel o ((absRegion bs r).natF g.val i.val) := by
  rw [nat_f] at h
  peel h as i1, hi1
  have e := region_fld_eq bs (r := r) hi1
  simp only [Region.natF]
  rw [← e]
  exact region_nat_sat_eq h

open ConLeche.Frontend.Olean in
/-- **`name_list` is `Region.nameList`.** -/
theorem name_list_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : name_list bs r g i = ok o) :
    o.map (fun v => v.val.map absWord) = (absRegion bs r).nameList g.val i.val := by
  rw [name_list] at h
  peel h as i1, hi1
  have e := region_fld_eq bs (r := r) hi1
  simp only [Region.nameList]
  rw [← e, ← region_list_eq h]
  cases o <;> simp [absWords]

/-- A pure index loop that declines with `none`, against `List.mapM` at `Option`: `hstep`
is one turn, whose answer is the twin's answer on that element. -/
theorem opt_vec_map {ξ ξ' α β : Type} {S : ξ → ξ' → Prop} {R : α → β → Prop}
    {src : List ξ} {xs : List ξ'} (hxs : List.Forall₂ S src xs) {t : ξ' → Option β}
    {loop : alloc.vec.Vec α → Std.Usize → Result (Option (alloc.vec.Vec α))}
    (hdone : ∀ out i, src.length ≤ i.val → loop out i = ok (some out))
    (hstep : ∀ (i : Std.Usize) (out : alloc.vec.Vec α) x x' o, src[i.val]? = some x → S x x' →
      loop out i = ok o →
      (t x' = none ∧ o = none) ∨
      ∃ (a : α) (b : β) (out1 : alloc.vec.Vec α) (i1 : Std.Usize), t x' = some b ∧ R a b ∧ out1.val = out.val ++ [a] ∧
        i1.val = i.val + 1 ∧ loop out1 i1 = ok o)
    {out : alloc.vec.Vec α} {i : Std.Usize} {o} (h0 : out.val = []) (hi : i.val = 0)
    (h : loop out i = ok o) :
    Option.Rel (fun v l => List.Forall₂ R v.val l) o (xs.mapM t) := by
  have aux : ∀ {src1 : List ξ} {xs1 : List ξ'}, List.Forall₂ S src1 xs1 →
      ∀ (i : Std.Usize) (out : alloc.vec.Vec α) (pre : List β) o, src.drop i.val = src1 →
        List.Forall₂ R out.val pre → loop out i = ok o →
        Option.Rel (fun v l => List.Forall₂ R v.val (pre ++ l)) o (xs1.mapM t) := by
    intro src1 xs1 hF
    induction hF with
    | nil =>
      intro i out pre o hd hpre h
      rw [hdone _ _ (List.drop_eq_nil_iff.mp hd)] at h
      cases Result.ok_injective h
      exact Option.Rel.some (by simpa using hpre)
    | @cons x x' src2 xs2 hS _ ih =>
      intro i out pre o hd hpre h
      have hlt : i.val < src.length := by
        apply Classical.byContradiction
        intro hn
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        cases hd
      rw [List.drop_eq_getElem_cons hlt] at hd
      obtain ⟨hx, hd2⟩ := List.cons.inj hd
      rw [List.mapM_cons]
      rcases hstep i out x x' o (by rw [List.getElem?_eq_getElem hlt, hx]) hS h with
        ⟨ht, rfl⟩ | ⟨a, b, out1, i1, ht, hR, ho, hi1, hl⟩
      · rw [ht]; exact Option.Rel.none
      · rw [ht]
        have := ih i1 out1 (pre ++ [b]) o (by rw [hi1]; exact hd2)
          (by rw [ho]; exact List.rel_append hpre (List.Forall₂.cons hR List.Forall₂.nil)) hl
        revert this
        show _ → Option.Rel _ o ((xs2.mapM t) >>= fun bs => pure (b :: bs))
        cases xs2.mapM t with
        | none => intro hn; cases hn; exact Option.Rel.none
        | some l =>
          intro hn
          cases hn with
          | some hn => exact Option.Rel.some (by simpa using hn)
  have := aux hxs i out [] o (by rw [hi]; rfl) (by rw [h0]; exact List.Forall₂.nil) h
  simpa using this

/-! ## One step of a skeleton

A skeleton reads one field after another, each failing to `none` on both sides. -/

/-- `ptrFld` at a literal field. -/
theorem ptr_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : region_ptr_fld bs r g i = ok o) (hk : i.val = k := by rfl) :
    o.map absWord = (absRegion bs r).ptrFld g.val k := by
  subst hk; exact region_ptr_fld_eq bs h

/-- `bool` at a literal byte. -/
theorem bool_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : region_bool bs r g i = ok o) (hk : i.val = k := by rfl) :
    o = (absRegion bs r).bool g.val k := by
  subst hk; exact region_bool_eq bs h

/-- `u8` at a literal byte. -/
theorem u8_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : region_u8 bs r g i = ok o) (hk : i.val = k := by rfl) :
    o.map absByte = (absRegion bs r).u8 g.val k := by
  subst hk; exact region_u8_eq bs h

/-- `u32` at a literal byte. -/
theorem u32_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : region_u32 bs r g i = ok o) (hk : i.val = k := by rfl) :
    o.map ConRon.Refine2.absU32 = (absRegion bs r).u32 g.val k := by
  subst hk; exact region_u32_eq bs h

/-- `isCtor` at a literal tag and field count. -/
theorem ctor_at (bs : Slice Std.U8) (t n : Nat) {r : frontend.olean.region.Region} {g t' n' : Std.U64}
    {b : Bool} (h : region_is_ctor bs r g t' n' = ok b) (ht : t'.val = t := by rfl)
    (hn : n'.val = n := by rfl) : b = (absRegion bs r).isCtor g.val t n := by
  subst ht; subst hn; exact region_is_ctor_eq bs h

/-- `nat_f` at a literal field, as upstream's `natP` on the field. -/
theorem nat_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : nat_f bs r g i = ok o) (hk : i.val = k := by rfl) :
    Option.Rel SatRel o ((absRegion bs r).natP g.val ((absRegion bs r).fld g.val k)) := by
  subst hk; exact nat_f_eq h

/-- `name_list` at a literal field. -/
theorem list_at (bs : Slice Std.U8) (k : Nat) {r : frontend.olean.region.Region} {g i : Std.U64} {o}
    (h : name_list bs r g i = ok o) (hk : i.val = k := by rfl) :
    o.map (fun v => v.val.map absWord) = (absRegion bs r).nameList g.val k := by
  subst hk; exact name_list_eq h

/-- The saturated read of a number: upstream's `none`, or the word and its `Nat`. -/
theorem sat_elim {α β : Type} {R : α → β → Prop} {P : Prop} {o : Option α} {y : Option β}
    (h : Option.Rel R o y)
    (hn : o = Option.none → y = Option.none → P)
    (hs : ∀ k n, o = Option.some k → y = Option.some n → R k n → P) : P := by
  cases h with
  | none => exact hn rfl rfl
  | some h => exact hs _ _ rfl rfl h

/-- Upstream's `bind`s and `pure`s at `Option`, one step on. -/
macro "opt_clean" : tactic =>
  `(tactic| try simp only [ConLeche.Frontend.Olean.Region.natF, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.map_none])

/-- Both sides have declined. -/
macro "opt_close " h:ident : tactic =>
  `(tactic| (cases Result.ok_injective $h:ident; first | rfl | exact Option.Rel.none))

/-- `let o ← read; match o with …`, against upstream's read `e` says is the same. -/
macro "opt_step " h:ident " as " v:rcasesPat " by " e:term : tactic =>
  `(tactic| (peel $h:ident as o1, ho1
             have he := $e ho1
             rw [← he]
             clear he
             rcases o1 with _ | $v
             · opt_close $h
             dsimp only at $h:ident
             opt_clean))

/-- `if !is_ctor { return None }`, against upstream's `unless`. -/
macro "ctor_step " h:ident " by " e:term : tactic =>
  `(tactic| (peel $h:ident as b, hb
             have he := $e hb
             rw [← he]
             clear he
             rcases b with _ | _
             · rw [ite_eq_right Bool.false_ne_true] at $h:ident
               rw [ite_eq_right Bool.false_ne_true]
               opt_close $h
             rw [ite_eq_left rfl] at $h:ident
             rw [ite_eq_left rfl]
             opt_clean))

/-- A saturated number. -/
macro "sat_opt " h:ident " as " v:ident n:ident hk:ident " by " e:term : tactic =>
  `(tactic| (peel $h:ident as o1, ho1
             refine sat_elim ($e ho1) (fun hA hy => ?_) (fun $v:ident $n:ident hA hy $hk:ident => ?_)
             · subst hA; rw [hy]; opt_close $h
             subst hA; rw [hy]
             dsimp only at $h:ident
             opt_clean))

/-! ## The skeletons -/

open ConLeche.Frontend.Olean in
/-- **`hints_skel` is `hintsSkel`.** -/
theorem hints_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x hv : Std.U64} {o}
    (h : hints_skel bs r x hv = ok o) :
    o.map absHintsRec = hintsSkel (absRegion bs r) x.val (absWord hv) := by
  rw [hints_skel] at h
  simp only [hintsSkel]
  split at h
  · rename_i h1
    rw [ite_eq_left (word_eq_one.mpr h1)]
    cases Result.ok_injective h
    rfl
  · rename_i h1
    rw [ite_eq_right (fun he => h1 (word_eq_one.mp he))]
    split at h
    · rename_i h3
      subst h3
      rw [ite_eq_left (by decide)]
      cases Result.ok_injective h
      rfl
    · rename_i h3
      rw [ite_eq_right (fun he => h3 (absWord_inj (a := hv) (b := 3#u64) (beq_iff_eq.mp he)))]
      opt_clean
      opt_step h as c by region_down_eq bs
      ctor_step h by ctor_at bs 2 0
      opt_step h as k by u32_at bs 0
      peel h as i, hi
      cases Result.ok_injective h
      simp only [lift] at hi
      cases Result.ok_injective hi
      simp [absHintsRec, absU64, UScalar.cast_val_eq, ConRon.Refine2.absU32]
      scalar_tac

/-- A string the skeleton spells. -/
theorem lit_str {n : Std.Usize} {M : Std.Array Std.U32 n} {S : String} {sl v}
    (hsl : lift (Std.Array.to_slice M) = ok sl) (hv : kernel.core_types.code_points sl = ok v)
    (hw : ∀ c ∈ M.val, Nat.isValidChar c.val)
    (hS : String.ofList (M.val.map fun c => Char.ofNat c.val) = S) :
    ConRon.Refine.absString v = S ∧ StrWF v := by
  simp only [lift] at hsl
  cases Result.ok_injective hsl
  have e : v.val = M.val := by
    rw [ConRon.Refine.Env.code_points_val hv]; simp
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString, e]; exact hS
  · intro c hc; rw [e] at hc; exact hw c hc

/-- Two different bytes stay different. -/
theorem absByte_ne {i k : Std.U8} (h : i = k → False) : absByte i ≠ absByte k := fun he =>
  h (UScalar.eq_of_val_eq (by simpa using congrArg UInt8.toNat he))

/-- A recursor rule. -/
theorem rule_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x v : Std.U64} {o}
    (h : rule_skel bs r x v = ok o) :
    Option.Rel (RuleRel absWord absWord SatRel) o
      (ConLeche.Frontend.Olean.ruleSkel (absRegion bs r) x.val (absWord v)) := by
  rw [rule_skel] at h
  simp only [ConLeche.Frontend.Olean.ruleSkel]
  opt_clean
  opt_step h as y by region_down_eq bs
  ctor_step h by ctor_at bs 0 3
  opt_step h as c by ptr_at bs 0
  sat_opt h as k' n hk by nat_at bs 1
  opt_step h as e by ptr_at bs 2
  cases Result.ok_injective h
  exact Option.Rel.some ⟨rfl, hk, rfl⟩

/-- **`rules_skel` is upstream's `mapM`.** -/
theorem rules_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x : Std.U64}
    {cells : alloc.vec.Vec Std.U64} {o} (h : rules_skel bs r x cells = ok o) :
    Option.Rel (fun v l => List.Forall₂ (RuleRel absWord absWord SatRel) v.val l) o
      ((cells.val.map absWord).mapM (ConLeche.Frontend.Olean.ruleSkel (absRegion bs r) x.val)) := by
  rw [rules_skel] at h
  refine opt_vec_map (forall₂_of_map (A := absWord) cells.val) ?_ ?_
    (loop := frontend.olean.spec.rules_skel_loop bs r x cells) (by simp) (by rfl) h
  · intro out i hi
    rw [frontend.olean.spec.rules_skel_loop, ite_eq_right (by scalar_tac)]
  · intro i out y y' o hy hS hl
    cases hS
    rw [frontend.olean.spec.rules_skel_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hy).1; scalar_tac)] at hl
    peel hl as y2, hy2
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy2
    rw [hy] at hy3
    cases Option.some.inj hy3
    peel hl as o1, ho1
    refine sat_elim (rule_skel_eq (bs := bs) (r := r) ho1) (fun hA hy => ?_)
      (fun ru b hA hy hR => ?_)
    · subst hA
      left; exact ⟨hy, (Result.ok_injective hl).symm⟩
    · subst hA
      right
      dsimp only at hl
      peel hl as out1, ho
      peel hl as i3, hi3
      exact ⟨ru, b, out1, i3, hy, hR, ConRon.Refine.vec_push_val ho, uscalar_add_eq hi3, hl⟩

open ConLeche.Frontend.Olean in
/-- **The definition arm of `kindSkel`.** -/
theorem kind_skel_defn_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x : Std.U64} {o}
    (h : kind_skel_defn bs r x = ok o) :
    Option.Rel (KindRel absWord absWord SatRel) o (kindSkel (absRegion bs r) 1 x.val) := by
  rw [kind_skel_defn] at h
  simp only [kindSkel]
  opt_clean
  ctor_step h by ctor_at bs 0 4
  opt_step h as value by ptr_at bs 1
  peel h as i, hi
  rw [fld_2 hi]
  opt_step h as hints by hints_skel_eq
  opt_step h as i1 by u8_at bs 0
  split at h
  · peel h as sl, hsl
    peel h as v, hv
    cases Result.ok_injective h
    obtain ⟨e, w⟩ := lit_str (S := "unsafe") hsl hv (by unfold frontend.olean.spec.kind_skel_defn.M; decide)
      (by unfold frontend.olean.spec.kind_skel_defn.M; rfl)
    exact Option.Rel.some (⟨rfl, rfl, e, w⟩ : _ ∧ _ ∧ _ ∧ _)
  · peel h as sl, hsl
    peel h as v, hv
    cases Result.ok_injective h
    obtain ⟨e, w⟩ := lit_str (S := "safe") hsl hv (by unfold frontend.olean.spec.kind_skel_defn.M_1; decide)
      (by unfold frontend.olean.spec.kind_skel_defn.M_1; rfl)
    exact Option.Rel.some (⟨rfl, rfl, e, w⟩ : _ ∧ _ ∧ _ ∧ _)
  · peel h as sl, hsl
    peel h as v, hv
    cases Result.ok_injective h
    obtain ⟨e, w⟩ := lit_str (S := "partial") hsl hv (by unfold frontend.olean.spec.kind_skel_defn.M_2; decide)
      (by unfold frontend.olean.spec.kind_skel_defn.M_2; rfl)
    exact Option.Rel.some (⟨rfl, rfl, e, w⟩ : _ ∧ _ ∧ _ ∧ _)
  · rename_i h0 h1 h2
    have a0 := absByte_ne h0
    have a1 := absByte_ne h1
    have a2 := absByte_ne h2
    cases Result.ok_injective h
    split
    · exact absurd ‹_› a0
    · exact absurd ‹_› a1
    · exact absurd ‹_› a2
    · exact Option.Rel.none

open ConLeche.Frontend.Olean in
/-- **The inductive-type arm of `kindSkel`.** -/
theorem kind_skel_induct_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x : Std.U64} {o}
    (h : kind_skel_induct bs r x = ok o) :
    Option.Rel (KindRel absWord absWord SatRel) o (kindSkel (absRegion bs r) 5 x.val) := by
  rw [kind_skel_induct] at h
  simp only [kindSkel]
  opt_clean
  ctor_step h by ctor_at bs 0 6
  sat_opt h as np n1 h1 by nat_at bs 1
  sat_opt h as ni n2 h2 by nat_at bs 2
  opt_step h as all by list_at bs 3
  opt_step h as cs by list_at bs 4
  sat_opt h as nn n3 h3 by nat_at bs 5
  opt_step h as ir by bool_at bs 0
  opt_step h as iu by bool_at bs 1
  opt_step h as irf by bool_at bs 2
  cases Result.ok_injective h
  exact Option.Rel.some (⟨h1, h2, rfl, rfl, h3, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)

open ConLeche.Frontend.Olean in
/-- **The recursor arm of `kindSkel`.** -/
theorem kind_skel_recur_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {x : Std.U64} {o}
    (h : kind_skel_recur bs r x = ok o) :
    Option.Rel (KindRel absWord absWord SatRel) o (kindSkel (absRegion bs r) 7 x.val) := by
  rw [kind_skel_recur] at h
  simp only [kindSkel]
  opt_clean
  ctor_step h by ctor_at bs 0 7
  opt_step h as all by list_at bs 1
  peel h as i, hi
  rw [show (absRegion bs r).fld x.val 6 = absWord i from (region_fld_eq bs hi).symm]
  opt_step h as cells by region_list_eq
  rw [show (absWords cells).toList = cells.val.map absWord by simp [absWords]]
  sat_opt h as rules rules' hR by rules_skel_eq
  sat_opt h as np n1 h1 by nat_at bs 2
  sat_opt h as ni n2 h2 by nat_at bs 3
  sat_opt h as nmo n3 h3 by nat_at bs 4
  sat_opt h as nmi n4 h4 by nat_at bs 5
  opt_step h as k by bool_at bs 0
  opt_step h as iu by bool_at bs 1
  cases Result.ok_injective h
  exact Option.Rel.some (⟨rfl, h1, h2, h3, h4, hR, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)

open ConLeche.Frontend.Olean in
/-- **`kind_skel` is `kindSkel`.** -/
theorem kind_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {t x : Std.U64} {o}
    (h : kind_skel bs r t x = ok o) :
    Option.Rel (KindRel absWord absWord SatRel) o (kindSkel (absRegion bs r) t.val x.val) := by
  rw [kind_skel] at h
  split at h
  · rename_i hT
    subst hT
    show Option.Rel _ _ (kindSkel (absRegion bs r) 0 x.val)
    simp only [kindSkel]
    opt_clean
    ctor_step h by ctor_at bs 0 1
    opt_step h as u by bool_at bs 0
    cases Result.ok_injective h
    exact Option.Rel.some rfl
  rename_i h0
  split at h
  · rename_i hT
    subst hT
    exact kind_skel_defn_eq h
  rename_i h1
  split at h
  · rename_i hT
    subst hT
    show Option.Rel _ _ (kindSkel (absRegion bs r) 2 x.val)
    simp only [kindSkel]
    opt_clean
    ctor_step h by ctor_at bs 0 3
    opt_step h as v by ptr_at bs 1
    opt_step h as all by list_at bs 2
    cases Result.ok_injective h
    exact Option.Rel.some (⟨rfl, rfl⟩ : _ ∧ _)
  rename_i h2
  split at h
  · rename_i hT
    subst hT
    show Option.Rel _ _ (kindSkel (absRegion bs r) 3 x.val)
    simp only [kindSkel]
    opt_clean
    ctor_step h by ctor_at bs 0 3
    opt_step h as v by ptr_at bs 1
    opt_step h as u by bool_at bs 0
    cases Result.ok_injective h
    exact Option.Rel.some (⟨rfl, rfl⟩ : _ ∧ _)
  rename_i h3
  split at h
  · rename_i hT
    subst hT
    show Option.Rel _ _ (kindSkel (absRegion bs r) 4 x.val)
    simp only [kindSkel]
    opt_clean
    ctor_step h by ctor_at bs 0 1
    opt_step h as i1 by u8_at bs 0
    split at h
    · peel h as sl, hsl
      peel h as v, hv
      cases Result.ok_injective h
      obtain ⟨e, w⟩ := lit_str (S := "type") hsl hv (by unfold frontend.olean.spec.kind_skel.M; decide)
        (by unfold frontend.olean.spec.kind_skel.M; rfl)
      exact Option.Rel.some (⟨e, w⟩ : _ ∧ _)
    · peel h as sl, hsl
      peel h as v, hv
      cases Result.ok_injective h
      obtain ⟨e, w⟩ := lit_str (S := "ctor") hsl hv (by unfold frontend.olean.spec.kind_skel.M_1; decide)
        (by unfold frontend.olean.spec.kind_skel.M_1; rfl)
      exact Option.Rel.some (⟨e, w⟩ : _ ∧ _)
    · peel h as sl, hsl
      peel h as v, hv
      cases Result.ok_injective h
      obtain ⟨e, w⟩ := lit_str (S := "lift") hsl hv (by unfold frontend.olean.spec.kind_skel.M_2; decide)
        (by unfold frontend.olean.spec.kind_skel.M_2; rfl)
      exact Option.Rel.some (⟨e, w⟩ : _ ∧ _)
    · peel h as sl, hsl
      peel h as v, hv
      cases Result.ok_injective h
      obtain ⟨e, w⟩ := lit_str (S := "ind") hsl hv (by unfold frontend.olean.spec.kind_skel.M_3; decide)
        (by unfold frontend.olean.spec.kind_skel.M_3; rfl)
      exact Option.Rel.some (⟨e, w⟩ : _ ∧ _)
    · rename_i b0 b1 b2 b3
      have a0 := absByte_ne b0
      have a1 := absByte_ne b1
      have a2 := absByte_ne b2
      have a3 := absByte_ne b3
      cases Result.ok_injective h
      split
      · exact absurd ‹_› a0
      · exact absurd ‹_› a1
      · exact absurd ‹_› a2
      · exact absurd ‹_› a3
      · exact Option.Rel.none
  rename_i h4
  split at h
  · rename_i hT
    subst hT
    exact kind_skel_induct_eq h
  rename_i h5
  split at h
  · rename_i hT
    subst hT
    show Option.Rel _ _ (kindSkel (absRegion bs r) 6 x.val)
    simp only [kindSkel]
    opt_clean
    ctor_step h by ctor_at bs 0 5
    opt_step h as ind by ptr_at bs 1
    sat_opt h as ci n1 k1 by nat_at bs 2
    sat_opt h as np n2 k2 by nat_at bs 3
    sat_opt h as nf n3 k3 by nat_at bs 4
    opt_step h as iu by bool_at bs 0
    cases Result.ok_injective h
    exact Option.Rel.some (⟨rfl, k1, k2, k3, rfl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _)
  rename_i h6
  have hrec := kind_skel_recur_eq h
  have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
  have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
  have e2 : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq he)
  have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
  have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
  have e5 : t.val ≠ 5 := fun he => h5 (UScalar.eq_of_val_eq he)
  have e6 : t.val ≠ 6 := fun he => h6 (UScalar.eq_of_val_eq he)
  generalize UScalar.val t = T at e0 e1 e2 e3 e4 e5 e6 ⊢
  rcases T with _ | _ | _ | _ | _ | _ | _ | T
  · exact absurd rfl e0
  · exact absurd rfl e1
  · exact absurd rfl e2
  · exact absurd rfl e3
  · exact absurd rfl e4
  · exact absurd rfl e5
  · exact absurd rfl e6
  · exact hrec

open ConLeche.Frontend.Olean in
/-- **`const_skel` is `constSkel`.** -/
theorem const_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {c : Std.U64} {o}
    (h : const_skel bs r c = ok o) :
    Option.Rel SkelRel o (constSkel (absRegion bs r) c.val) := by
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  rw [const_skel] at h
  simp only [constSkel]
  peel h as i, hi
  rw [← region_nobjs_eq bs hi]
  split at h
  · rename_i h1
    subst h1
    peel h as i1, hi1
    rw [← region_tag_eq bs hi1]
    split at h
    · rename_i h2
      have hv2 : i1.val ≤ 7 := by scalar_tac
      peel h as b, hb
      rw [← region_fits_eq bs hb]
      split at h
      · rename_i h3
        rw [ite_eq_left (by simp [l1, hv2, h3])]
        opt_clean
        peel h as i2, hi2
        rw [fld_0 hi2]
        opt_step h as x by region_down_eq bs
        peel h as i3, hi3
        rw [← region_nobjs_eq bs hi3]
        split at h
        · rename_i h4
          have hv4 : 1 ≤ i3.val := by scalar_tac
          peel h as b1, hb1
          rw [← region_fits_eq bs hb1]
          split at h
          · rename_i h5
            rw [ite_eq_left (by simp [hv4, h5])]
            peel h as i4, hi4
            rw [fld_0 hi4]
            opt_step h as cv by region_down_eq bs
            ctor_step h by ctor_at bs 0 3
            opt_step h as v by ptr_at bs 0
            opt_step h as v1 by list_at bs 1
            opt_step h as v2 by ptr_at bs 2
            sat_opt h as kind kind' hK by kind_skel_eq
            cases Result.ok_injective h
            exact Option.Rel.some ⟨rfl, rfl, rfl, hK⟩
          · rename_i h5
            rw [ite_eq_right (by simp [h5])]
            opt_close h
        · rename_i h4
          have hv4 : ¬ 1 ≤ i3.val := by scalar_tac
          rw [ite_eq_right (by simp [hv4])]
          opt_close h
      · rename_i h3
        rw [ite_eq_right (by simp [h3])]
        opt_close h
    · rename_i h2
      have hv2 : ¬ i1.val ≤ 7 := by scalar_tac
      rw [ite_eq_right (by simp [hv2])]
      opt_close h
  · rename_i h1
    have hv : i.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq (by rw [he, l1]))
    rw [ite_eq_right (by simp [hv])]
    opt_close h

/-- An `ImportF`, its name abstracted. -/
def absImportF {N N' : Type} (A : N → N') (i : frontend.olean.spec.ImportF N) : ImportF N' :=
  ⟨A i.module, i.import_all, i.is_exported, i.is_meta⟩

open ConLeche.Frontend.Olean in
/-- **`import_skel` is `importSkel`.** -/
theorem import_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {i : Std.U64} {o}
    (h : import_skel bs r i = ok o) :
    o.map (absImportF absWord) = importSkel (absRegion bs r) i.val := by
  rw [import_skel] at h
  simp only [importSkel]
  opt_clean
  ctor_step h by ctor_at bs 0 1
  opt_step h as module by ptr_at bs 0
  opt_step h as ia by bool_at bs 0
  opt_step h as ie by bool_at bs 1
  opt_step h as im by bool_at bs 2
  cases Result.ok_injective h
  rfl

open ConLeche.Frontend.Olean in
/-- **`imports_skel` is upstream's `mapM`.** -/
theorem imports_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {imps : alloc.vec.Vec Std.U64} {o} (h : imports_skel bs r imps = ok o) :
    o.map (fun v => v.val.map (absImportF absWord)) =
      (imps.val.map (·.val)).mapM (importSkel (absRegion bs r)) := by
  rw [imports_skel] at h
  have e := opt_vec_map (R := EqA (absImportF absWord))
    (forall₂_of_map (A := fun v : Std.U64 => v.val) imps.val)
    (t := importSkel (absRegion bs r))
    (loop := frontend.olean.spec.imports_skel_loop bs r imps) ?_ ?_ (by simp) (by rfl) h
  · refine sat_elim e (fun hA hy => ?_) (fun a b hA hy hR => ?_)
    · subst hA; rw [hy]; rfl
    · subst hA; rw [hy]
      exact congrArg _ (forall₂_eqA hR)
  · intro out i hi
    rw [frontend.olean.spec.imports_skel_loop, ite_eq_right (by scalar_tac)]
  · intro i out y y' o hy hS hl
    cases hS
    rw [frontend.olean.spec.imports_skel_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hy).1; scalar_tac)] at hl
    peel hl as y2, hy2
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy2
    rw [hy] at hy3
    cases Option.some.inj hy3
    peel hl as o1, ho1
    have e := import_skel_eq (bs := bs) (r := r) ho1
    rw [← e]
    cases o1 with
    | none => left; exact ⟨rfl, (Result.ok_injective hl).symm⟩
    | some ru =>
      right
      dsimp only at hl
      peel hl as out1, ho
      peel hl as i3, hi3
      exact ⟨ru, _, out1, i3, rfl, rfl, ConRon.Refine.vec_push_val ho, uscalar_add_eq hi3, hl⟩

/-- **`spec::ModSkel` against upstream's.** -/
structure ModSkelRel (m : frontend.olean.spec.ModSkel) (m' : ModSkel) : Prop where
  isModule : m.is_module = m'.isModule
  imports : m.imports.val.map (absImportF absWord) = m'.imports
  consts : m.consts.val.map (·.val) = m'.consts

open ConLeche.Frontend.Olean in
/-- **`module_skel` is `moduleSkel`.** -/
theorem module_skel_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {root : Std.U64} {o}
    (hr : RegionFits bs r) (h : module_skel bs r root = ok o) :
    Option.Rel ModSkelRel o (moduleSkel (absRegion bs r) (absWord root)) := by
  rw [module_skel] at h
  simp only [moduleSkel]
  opt_clean
  opt_step h as g by region_loc_eq bs
  ctor_step h by ctor_at bs 0 5
  opt_step h as b1 by bool_at bs 0
  peel h as i, hi
  rw [fld_0 hi]
  opt_step h as v by region_obj_array_eq hr
  rw [show (absLocs v).toList = v.val.map (·.val) by simp [absLocs]]
  opt_step h as v1 by imports_skel_eq
  peel h as i1, hi1
  rw [fld_2 hi1]
  opt_step h as consts by region_obj_array_eq hr
  cases Result.ok_injective h
  exact Option.Rel.some ⟨rfl, rfl, by simp [absLocs]⟩

end ConRon.Refine2.Frontend.Olean

/-
# `ConRon.Refine2.Frontend.Olean.SpecEntry` — a constant's reads, and the name table

**Task #142, Theorem 2.**  The second half of `olean/spec.rs`: `PtrRead`, with
`CEntryF.mapM` at `OptionT AM`; the pins; `skel_fits`; the imports; the name-table check.
-/
import ConRon.Refine2.Frontend.Olean.Spec
import ConRon.Refine2.Dup

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_fld region_down region_tag region_nobjs region_fits
  region_str_p region_nat_sat region_nat_p region_is_ctor region_loc region_obj_array)
open frontend.olean.spec (nat_word name_tail names_map names_map_loop rules_map rules_map_loop
  c_kind_map c_entry_map hints_dup import_map)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (entryMap)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF)
open ConRon.Refine.HashMap (uscalar_add_eq)

/-! ## `PtrRead` -/

/-- **A `PtrRead` instance's reads are a twin `PtrRead`'s.** -/
structure PtrRel {R : Type} (inst : frontend.olean.spec.PtrRead R) (rd : R)
    (t : Arena.Frontend.Olean.PtrRead) (pk : frontend.olean.spec.OleanPins) (bs : Slice Std.U8)
    (r : frontend.olean.region.Region) (pers : arena.store.PersTier) : Prop where
  nm : ∀ st lst v, RS pers (EqA absNIdx) st lst (inst.rd_name rd pk pers st.store bs r v)
    (t.rdName (absWord v))
  ex : ∀ st lst v, RS pers (EqA absEIdx) st lst (inst.rd_expr rd pk pers st.store bs r v)
    (t.rdExpr (absWord v))

/-- **`names_map` is `all.mapM`**, at `OptionT AM`. -/
theorem names_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {ns : alloc.vec.Vec Std.U64} {l : List UInt64} (hl : ListA absWord ns l) (st lst) :
    RS pers (ListA absNIdx) st lst (names_map inst rd pk pers st.store bs r ns)
      (l.mapM (m := OptionT AM) fun v => OptionT.mk (t.rdName v)) := by
  subst hl
  rw [names_map]
  refine RS.mono (RS.vec_map (R := EqA absNIdx)
    (loop := fun ar out i => names_map_loop inst rd pk pers ar bs r ns out i)
    (forall₂_of_map (A := absWord) ns.val) ?_ ?_ (by simp) (by rfl))
    (fun a b hab => forall₂_eqA hab)
  · intro ar out i hi
    show names_map_loop inst rd pk pers ar bs r ns out i = _
    rw [names_map_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (names_map_loop inst rd pk pers st.store bs r ns out i) _
    rw [names_map_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (hp.nm st lst x) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`rules_map` is `rules.mapM`**, at `OptionT AM`: `q` is the twin's function on a rule. -/
theorem rules_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {rs : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)} {l : List (UInt64 × Nat × UInt64)}
    (hl : List.Forall₂ (RuleRel absWord absWord ValRel) rs.val l)
    {q : UInt64 × Nat × UInt64 → OptionT AM (NIdx × Nat × EIdx)}
    (hq : ∀ c n e, q (c, n, e) = (OptionT.mk (t.rdName c) >>= fun c' =>
      OptionT.mk (t.rdExpr e) >>= fun e' => pure (c', n, e')))
    (st lst) :
    RS pers (fun v l' => List.Forall₂ (RuleRel absNIdx absEIdx ValRel) v.val l') st lst
      (rules_map inst rd pk pers st.store bs r rs) (l.mapM (m := OptionT AM) q) := by
  rw [rules_map]
  refine RS.vec_map (R := RuleRel absNIdx absEIdx ValRel)
    (loop := fun ar out i => rules_map_loop inst rd pk pers ar bs r rs out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show rules_map_loop inst rd pk pers ar bs r rs out i = _
    rw [rules_map_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (rules_map_loop inst rd pk pers st.store bs r rs out i) _
    rw [rules_map_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    obtain ⟨c, n, e⟩ := x
    obtain ⟨c', n', e'⟩ := x'
    obtain ⟨hc, hn, he⟩ := hS
    cases hc; cases he; cases hn
    rw [hq]
    simp only [bind_assoc, pure_bind]
    refine RS.bindT (hp.nm st lst c) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.bindT (hp.ex (withStore st s1) lst1 e) (fun _ _ => by rfl) fun a2 b2 s2 lst2 hR2 =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    cases hR; cases hR2
    exact hK (a, n, a2) (absNIdx a, n.val, absEIdx a2) s2 lst2 out1 i3 ⟨rfl, rfl, rfl⟩
      (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- `hints_dup` is the identity. -/
theorem hints_dup_val {h r : frontend.scan_types.HintsRec} (e : hints_dup h = ok r) : r = h := by
  cases h <;> exact (Result.ok_injective e).symm

/-- **`c_kind_map` is `CKindF.mapM`**, at `OptionT AM`. -/
theorem c_kind_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {k : frontend.olean.spec.CKindF Std.U64 Std.U64} {k' : CKindF UInt64 UInt64}
    (hk : KindRel absWord absWord ValRel k k') (st lst) :
    RS pers (KindRel absNIdx absEIdx ValRel) st lst (c_kind_map inst rd pk pers st.store bs r k)
      (k'.mapM (m := OptionT AM) (fun v => OptionT.mk (t.rdName v))
        (fun v => OptionT.mk (t.rdExpr v))) := by
  cases k <;> cases k' <;> try exact hk.elim
  all_goals simp only [c_kind_map, CKindF.mapM]
  case Ax.ax u u' =>
    cases (show u = u' from hk)
    exact RS.some rfl
  case Defn.defn v h s v' h' s' =>
    obtain ⟨rfl, rfl, rfl, w⟩ := hk
    refine RS.bindT (hp.ex st lst v) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun hr hhr => RS.pure_step fun v1 hv1 => ?_
    rw [hints_dup_val hhr, ConRon.Refine.Expr.str_copy_eq hv1]
    cases hR
    exact RS.some ⟨rfl, rfl, rfl, w⟩
  case Thm.thm v all v' all' =>
    obtain ⟨rfl, hl⟩ := hk
    refine RS.bindT (hp.ex st lst v) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.bindT (names_map_refines hp hl (withStore st s1) lst1) (fun _ _ => by rfl)
        fun a2 b2 s2 lst2 hR2 => ?_
    cases hR
    exact RS.some ⟨rfl, hR2⟩
  case Opaq.opaq v u v' u' =>
    obtain ⟨rfl, rfl⟩ := hk
    refine RS.bindT (hp.ex st lst v) (fun _ _ => by rfl) fun a b s1 lst1 hR => ?_
    cases hR
    exact RS.some ⟨rfl, rfl⟩
  case Quot.quot s s' =>
    obtain ⟨rfl, w⟩ := hk
    refine RS.pure_step fun v1 hv1 => ?_
    rw [ConRon.Refine.Expr.str_copy_eq hv1]
    exact RS.some ⟨rfl, w⟩
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨h1, h2, hl1, hl2, h3, rfl, rfl, rfl⟩ := hk
    refine RS.bindT (names_map_refines hp hl1 st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT (names_map_refines hp hl2 (withStore st s1) lst1)
        (fun _ _ => by rfl) fun a2 b2 s2 lst2 hR2 => ?_
    exact RS.some ⟨h1, h2, hR, hR2, h3, rfl, rfl, rfl⟩
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨rfl, h1, h2, h3, rfl⟩ := hk
    refine RS.bindT (hp.nm st lst ind) (fun _ _ => by rfl) fun a b s1 lst1 hR => ?_
    cases hR
    exact RS.some ⟨rfl, h1, h2, h3, rfl⟩
  case Recur.recur all np ni nmo nmi rules k2 iu all' np' ni' nmo' nmi' rules' k2' iu' =>
    obtain ⟨hl1, h1, h2, h3, h4, hl2, rfl, rfl⟩ := hk
    refine RS.bindT (names_map_refines hp hl1 st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT
        (rules_map_refines hp hl2 (fun _ _ _ => rfl) (withStore st s1) lst1)
        (fun _ _ => by rfl) fun a2 b2 s2 lst2 hR2 => ?_
    exact RS.some ⟨hR, h1, h2, h3, h4, hR2, rfl, rfl⟩

/-- **`c_entry_map` is `entryMap`.** -/
theorem c_entry_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {c : frontend.olean.spec.CEntryF Std.U64 Std.U64} {c' : CEntryF UInt64 UInt64}
    (hc : EntryRel absWord absWord ValRel c c') (st lst) :
    RS pers (EntryRel absNIdx absEIdx ValRel) st lst (c_entry_map inst rd pk pers st.store bs r c)
      (entryMap t c') := by
  obtain ⟨n', l', ty', k'⟩ := c'
  obtain ⟨rfl, hl, rfl, hk⟩ := hc
  rw [c_entry_map]
  show RS _ _ _ _ _ (CEntryF.mapM (m := OptionT AM) _ _ _)
  rw [CEntryF.mapM]
  refine RS.bindT (hp.nm st lst c.name) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
    RS.bindT (names_map_refines hp hl (withStore st s1) lst1) (fun _ _ => by rfl)
      fun a2 b2 s2 lst2 hR2 => RS.bindT (hp.ex (withStore (withStore st s1) s2) lst2 c.ty)
        (fun _ _ => by rfl) fun a3 b3 s3 lst3 hR3 => RS.bindT
          (c_kind_map_refines hp hk (withStore (withStore (withStore st s1) s2) s3) lst3)
          (fun _ _ => by rfl) fun a4 b4 s4 lst4 hR4 => ?_
  cases hR; cases hR3
  exact RS.some ⟨rfl, hR2, rfl, hR4⟩

/-- **`import_map` is `ImportF.mapM`**, at `OptionT AM`. -/
theorem import_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {i : frontend.olean.spec.ImportF Std.U64} (st lst) :
    RS pers (EqA (absImportF absNIdx)) st lst (import_map inst rd pk pers st.store bs r i)
      (ImportF.mapM (m := OptionT AM) (fun v => OptionT.mk (t.rdName v))
        (absImportF absWord i)) := by
  rw [import_map]
  show RS _ _ _ _ _ (OptionT.mk (t.rdName (absWord i.module)) >>= _ : OptionT AM _)
  refine RS.bindT (hp.nm st lst i.module) (fun _ _ => by rfl) fun a b s1 lst1 hR => ?_
  cases hR
  exact RS.some rfl

end ConRon.Refine2.Frontend.Olean

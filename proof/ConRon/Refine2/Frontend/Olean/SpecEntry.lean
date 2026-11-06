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

/-! ## The pins -/

/-- `intern_name`, in the store's own channel. -/
theorem CS.intern_name {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.store.NNodeView} (hv : NNodeViewWF v) :
    CS pers (EqA absNIdx) st lst (arena.store.EStore.intern_name st.store pers v)
      (internNNode (absNNodeView v)) := by
  intro hrel hinv o s' h
  have hS := intern_n_node_run₀ hrel hinv v hv (o := (o, withStore st s'))
    (by rw [arena.monad.intern_n_node, h]; simp only [bind_ok]; rfl)
  cases o with
  | Ok a =>
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    exact ⟨_, lst1, hx, rfl, hrel1, hinv1⟩
  | Err e => exact Sim₀.apply_err hS

/-- `intern_level`, in the store's own channel. -/
theorem CS.intern_level {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.store.LNodeView} :
    CS pers (EqA absLIdx) st lst (arena.store.EStore.intern_level st.store pers v)
      (internLNode (absLNodeView v)) := by
  intro hrel hinv o s' h
  have hS := intern_l_node_run₀ hrel hinv v (o := (o, withStore st s'))
    (by rw [arena.monad.intern_l_node, h]; simp only [bind_ok]; rfl)
  cases o with
  | Ok a =>
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    exact ⟨_, lst1, hx, rfl, hrel1, hinv1⟩
  | Err e => exact Sim₀.apply_err hS

/-- `intern_levels`, in the store's own channel. -/
theorem CS.intern_levels {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : alloc.vec.Vec arena.handle.LIdx} :
    CS pers (EqA absLsIdx) st lst (arena.store.EStore.intern_levels st.store pers v)
      (internLsNode (absLsNodeView v)) := by
  intro hrel hinv o s' h
  have hS := intern_ls_node_run₀ hrel hinv v (o := (o, withStore st s'))
    (by rw [arena.monad.intern_ls_node, h]; simp only [bind_ok]; rfl)
  cases o with
  | Ok a =>
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    exact ⟨_, lst1, hx, rfl, hrel1, hinv1⟩
  | Err e => exact Sim₀.apply_err hS

/-- `mk_n_step`, a name spelled by the reader. -/
theorem mk_n_step_refines {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {p : arena.handle.NIdx} {v : alloc.vec.Vec Std.U32} {S : String}
    (h : ConRon.Refine.absString v = S ∧ ConRon.Refine.StrWF v) :
    CS pers (EqA absNIdx) st lst (frontend.olean.spec.mk_n_step pers st.store p v)
      (internNNode (.str (absNIdx p) S)) := by
  rw [frontend.olean.spec.mk_n_step, ← h.1]
  exact CS.intern_name (v := .Str p v) h.2

/-- One name of the pins. -/
macro "pin_step " S:str M:ident : tactic =>
  `(tactic| (refine CS.pure_step fun s hs => CS.pure_step fun v hv => ?_
             refine CS.bind (mk_n_step_refines
                 (lit_str (S := $S) hs hv (by unfold $M:ident; decide) (by unfold $M:ident; rfl)))
               (fun _ _ => by rfl) fun a b s1 lst1 hR => ?_
             cases hR))

/-- **`olean_pins` is `oleanPins`.** -/
theorem olean_pins_refines {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState} :
    CS pers (fun a b => b = absPins a) st lst (frontend.olean.spec.olean_pins pers st.store)
      Arena.Frontend.Olean.oleanPins := by
  rw [frontend.olean.spec.olean_pins, Arena.Frontend.Olean.oleanPins]
  refine CS.bind (CS.intern_name (v := .Anonymous) trivial) (fun _ _ => by rfl)
    fun h b s1 lst1 hR => ?_
  cases hR
  refine CS.bind (CS.intern_level (v := .Zero)) (fun _ _ => by rfl)
    fun h1 b s1 lst1 hR => ?_
  cases hR
  refine CS.bind (CS.intern_levels (v := alloc.vec.Vec.new _)) (fun _ _ => by rfl)
    fun h2 b s1 lst1 hR => ?_
  cases hR
  refine CS.pure_step fun n hn => ?_
  obtain rfl := nidx_dup2_ok hn
  pin_step "Nat" frontend.olean.spec.olean_pins.M
  pin_step "Char" frontend.olean.spec.olean_pins.M_1
  pin_step "ofNat" frontend.olean.spec.olean_pins.M_2
  pin_step "String" frontend.olean.spec.olean_pins.M_3
  pin_step "ofList" frontend.olean.spec.olean_pins.M_4
  pin_step "Eq" frontend.olean.spec.olean_pins.M_5
  pin_step "Quot" frontend.olean.spec.olean_pins.M_6
  refine CS.pure_step fun n1 hn1 => ?_
  obtain rfl := nidx_dup2_ok hn1
  pin_step "mk" frontend.olean.spec.olean_pins.M_7
  pin_step "lift" frontend.olean.spec.olean_pins.M_8
  pin_step "ind" frontend.olean.spec.olean_pins.M_9
  exact CS.pure rfl


/-! ## `skelFits` -/

/-- `SatRel`'s test, as the twin's. -/
theorem sat_big {k : Std.U64} {n : Nat} (h : SatRel k n) :
    decide (k = core.num.U64.MAX) = decide (Arena.Frontend.Olean.wordMax ≤ n) := by
  have hw : Arena.Frontend.Olean.wordMax = 2 ^ 64 - 1 := rfl
  rw [hw]
  exact decide_eq_decide.mpr h.max_iff

/-- `rules_too_big`'s loop is the twin's `any`. -/
theorem rules_too_big_eq {N N' E E' : Type} {AN : N → N'} {AE : E → E'}
    {rules : alloc.vec.Vec (N × Std.U64 × E)} {l : List (N' × Nat × E')}
    (hl : List.Forall₂ (RuleRel AN AE SatRel) rules.val l) {b : Bool}
    (h : frontend.olean.spec.rules_too_big rules = ok b) :
    b = l.any fun x => decide (Arena.Frontend.Olean.wordMax ≤ x.2.1) := by
  have aux : ∀ {src1 : List (N × Std.U64 × E)} {l1 : List (N' × Nat × E')},
      List.Forall₂ (RuleRel AN AE SatRel) src1 l1 → ∀ (i : Std.Usize) (b : Bool),
        rules.val.drop i.val = src1 →
        frontend.olean.spec.rules_too_big_loop rules i = ok b →
        b = l1.any fun x => decide (Arena.Frontend.Olean.wordMax ≤ x.2.1) := by
    intro src1 l1 hF
    induction hF with
    | nil =>
      intro i b hd h
      have hle := List.drop_eq_nil_iff.mp hd
      rw [frontend.olean.spec.rules_too_big_loop, ite_eq_right (by scalar_tac)] at h
      cases Result.ok_injective h
      rfl
    | @cons x x' src2 l2 hS _ ih =>
      intro i b hd h
      have hlt : i.val < rules.val.length := by
        apply Classical.byContradiction
        intro hn
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        cases hd
      rw [List.drop_eq_getElem_cons hlt] at hd
      obtain ⟨hx, hd2⟩ := List.cons.inj hd
      rw [frontend.olean.spec.rules_too_big_loop, ite_eq_left (by scalar_tac)] at h
      peel h as y, hy
      have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
      rw [List.getElem?_eq_getElem hlt, hx] at hy3
      cases Option.some.inj hy3
      obtain ⟨c, k, e⟩ := x
      have hbig : decide (k = core.num.U64.MAX) = _ := sat_big hS.2.1
      have h : (if k = core.num.U64.MAX then ok true else do
          let i3 ← i + 1#usize
          frontend.olean.spec.rules_too_big_loop rules i3) = ok b := h
      rw [List.any_cons]
      split at h
      · rename_i hk
        cases Result.ok_injective h
        rw [← hbig]
        simp [hk]
      · rename_i hk
        peel h as i3, hi3
        have hiv := uscalar_add_eq hi3
        rw [← hbig, decide_eq_false hk, Bool.false_or]
        exact ih i3 b (by rw [hiv]; exact hd2) h
  exact aux hl 0#usize b (by rfl) h

/-- Rules no number of which is too big hold their values. -/
theorem rules_val {N N' E E' : Type} {AN : N → N'} {AE : E → E'}
    {l : List (N × Std.U64 × E)} {l' : List (N' × Nat × E')}
    (hl : List.Forall₂ (RuleRel AN AE SatRel) l l')
    (h : (l'.any fun x => decide (Arena.Frontend.Olean.wordMax ≤ x.2.1)) = false) :
    List.Forall₂ (RuleRel AN AE ValRel) l l' := by
  induction hl with
  | nil => exact List.Forall₂.nil
  | @cons x x' _ _ hS _ ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    refine List.Forall₂.cons ⟨hS.1, ?_, hS.2.2⟩ (ih h.2)
    have hb := sat_big hS.2.1
    rw [h.1] at hb
    exact hS.2.1.val_of_ne (of_decide_eq_false hb)

/-- What `skelFits` tests of a constant. -/
def twinBad {N E : Type} (c : CEntryF N E) : Bool :=
  match c.kind with
  | .induct np ni _ _ nn .. =>
    decide (Arena.Frontend.Olean.wordMax ≤ np) || decide (Arena.Frontend.Olean.wordMax ≤ ni) ||
      decide (Arena.Frontend.Olean.wordMax ≤ nn)
  | .ctor _ ci np nf _ =>
    decide (Arena.Frontend.Olean.wordMax ≤ ci) || decide (Arena.Frontend.Olean.wordMax ≤ np) ||
      decide (Arena.Frontend.Olean.wordMax ≤ nf)
  | .recur _ np ni nmo nmi rules .. =>
    decide (Arena.Frontend.Olean.wordMax ≤ np) || decide (Arena.Frontend.Olean.wordMax ≤ ni) ||
      decide (Arena.Frontend.Olean.wordMax ≤ nmo) || decide (Arena.Frontend.Olean.wordMax ≤ nmi) ||
      rules.any fun x => decide (Arena.Frontend.Olean.wordMax ≤ x.2.1)
  | _ => false

theorem skelFits_eq {N E : Type} (c : CEntryF N E) :
    Arena.Frontend.Olean.skelFits c =
      if twinBad c = true then
        (do let _ ← Arena.Frontend.Olean.natWord Arena.Frontend.Olean.wordMax; pure ())
      else pure () := by
  obtain ⟨_, _, _, k⟩ := c
  cases k <;> rfl

/-- Three numbers of a constant, tested in turn. -/
theorem bad3 {a b c : Std.U64} {A B C : Nat} {bad : Bool} (ha : SatRel a A) (hb : SatRel b B)
    (hc : SatRel c C)
    (h : (if a = core.num.U64.MAX then ok true else if b = core.num.U64.MAX then ok true
      else ok (decide (c = core.num.U64.MAX))) = ok bad) :
    bad = (decide (Arena.Frontend.Olean.wordMax ≤ A) || decide (Arena.Frontend.Olean.wordMax ≤ B) ||
      decide (Arena.Frontend.Olean.wordMax ≤ C)) ∧
    (bad = false → a.val = A ∧ b.val = B ∧ c.val = C) := by
  have e : bad = (decide (a = core.num.U64.MAX) || decide (b = core.num.U64.MAX) ||
      decide (c = core.num.U64.MAX)) := by
    by_cases h1 : a = core.num.U64.MAX
    · rw [ite_eq_left h1] at h
      cases Result.ok_injective h
      simp [h1]
    · rw [ite_eq_right h1] at h
      by_cases h2 : b = core.num.U64.MAX
      · rw [ite_eq_left h2] at h
        cases Result.ok_injective h
        simp [h2]
      · rw [ite_eq_right h2] at h
        cases Result.ok_injective h
        simp [h1, h2]
  refine ⟨by rw [e, sat_big ha, sat_big hb, sat_big hc], fun hf => ?_⟩
  rw [e] at hf
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
  exact ⟨ha.val_of_ne hf.1.1, hb.val_of_ne hf.1.2, hc.val_of_ne hf.2⟩

/-- **`skel_fits` is `skelFits`**: from there on a skeleton's numbers are their values. -/
theorem skel_fits_refines {c : frontend.olean.spec.CEntryF Std.U64 Std.U64}
    {c' : CEntryF UInt64 UInt64} (hc : SkelRel c c') {o}
    (h : frontend.olean.spec.skel_fits c = ok o) {lst : AState} :
    match o with
    | .Ok _ => (Arena.Frontend.Olean.skelFits c').run lst = .ok ((), lst) ∧
        EntryRel absWord absWord ValRel c c'
    | .Err .Bad => False
    | .Err (.Err e) => AErrSim e ((Arena.Frontend.Olean.skelFits c').run lst) := by
  rw [frontend.olean.spec.skel_fits] at h
  peel h as bad, hbad
  have key : bad = twinBad c' ∧ (bad = false → EntryRel absWord absWord ValRel c c') := by
    obtain ⟨cn, cl, cty, ck⟩ := c
    obtain ⟨c1, c2, c3, c4⟩ := c'
    obtain ⟨h1, h2, h3, hk⟩ := hc
    cases ck <;> cases c4 <;> try exact hk.elim
    case Ax.ax =>
      cases Result.ok_injective hbad
      exact ⟨rfl, fun _ => ⟨h1, h2, h3, hk⟩⟩
    case Defn.defn =>
      cases Result.ok_injective hbad
      exact ⟨rfl, fun _ => ⟨h1, h2, h3, hk⟩⟩
    case Thm.thm =>
      cases Result.ok_injective hbad
      exact ⟨rfl, fun _ => ⟨h1, h2, h3, hk⟩⟩
    case Opaq.opaq =>
      cases Result.ok_injective hbad
      exact ⟨rfl, fun _ => ⟨h1, h2, h3, hk⟩⟩
    case Quot.quot =>
      cases Result.ok_injective hbad
      exact ⟨rfl, fun _ => ⟨h1, h2, h3, hk⟩⟩
    case Induct.induct =>
      obtain ⟨n1, n2, l1, l2, n3, a1, a2, a3⟩ := hk
      obtain ⟨e, hv⟩ := bad3 n1 n2 n3 hbad
      refine ⟨e, fun hf => ?_⟩
      obtain ⟨v1, v2, v3⟩ := hv hf
      exact ⟨h1, h2, h3, v1, v2, l1, l2, v3, a1, a2, a3⟩
    case Ctor.ctor =>
      obtain ⟨n0, n1, n2, n3, a1⟩ := hk
      obtain ⟨e, hv⟩ := bad3 n1 n2 n3 hbad
      refine ⟨e, fun hf => ?_⟩
      obtain ⟨v1, v2, v3⟩ := hv hf
      exact ⟨h1, h2, h3, n0, v1, v2, v3, a1⟩
    case Recur.recur _a np ni nmo nmi _r _k _u _a' _np' _ni' _nmo' _nmi' _r' _k' _u' =>
      obtain ⟨l1, n1, n2, n3, n4, hr, a1, a2⟩ := hk
      have s1 := sat_big n1
      have s2 := sat_big n2
      have s3 := sat_big n3
      have s4 := sat_big n4
      dsimp only at hbad
      by_cases b1 : np = core.num.U64.MAX
      · rw [ite_eq_left b1] at hbad
        cases Result.ok_injective hbad
        rw [decide_eq_true b1] at s1
        simp [twinBad, ← s1]
      rw [ite_eq_right b1] at hbad
      by_cases b2 : ni = core.num.U64.MAX
      · rw [ite_eq_left b2] at hbad
        cases Result.ok_injective hbad
        rw [decide_eq_true b2] at s2
        simp [twinBad, ← s2]
      rw [ite_eq_right b2] at hbad
      by_cases b3 : nmo = core.num.U64.MAX
      · rw [ite_eq_left b3] at hbad
        cases Result.ok_injective hbad
        rw [decide_eq_true b3] at s3
        simp [twinBad, ← s3]
      rw [ite_eq_right b3] at hbad
      by_cases b4 : nmi = core.num.U64.MAX
      · rw [ite_eq_left b4] at hbad
        cases Result.ok_injective hbad
        rw [decide_eq_true b4] at s4
        simp [twinBad, ← s4]
      rw [ite_eq_right b4] at hbad
      have er := rules_too_big_eq hr hbad
      refine ⟨?_, fun hf => ?_⟩
      · simp only [twinBad]
        rw [← s1, ← s2, ← s3, ← s4, decide_eq_false b1, decide_eq_false b2, decide_eq_false b3,
          decide_eq_false b4, er]
        rfl
      · rw [er] at hf
        exact ⟨h1, h2, h3, l1, n1.val_of_ne b1, n2.val_of_ne b2, n3.val_of_ne b3,
          n4.val_of_ne b4, rules_val hr hf, a1, a2⟩
  obtain ⟨e, hv⟩ := key
  rw [skelFits_eq, ← e]
  cases bad with
  | false =>
    rw [ite_eq_right Bool.false_ne_true] at h ⊢
    cases Result.ok_injective h
    exact ⟨rfl, hv rfl⟩
  | true =>
    rw [ite_eq_left rfl] at h ⊢
    peel h as r0, hr0
    have hm : ∃ e, r0 = .Err (.Err e) := by
      rw [nat_word, ite_eq_left rfl] at hr0
      peel hr0 as s0, -
      peel hr0 as v0, -
      peel hr0 as ce, -
      exact ⟨ce, (Result.ok_injective hr0).symm⟩
    obtain ⟨ce, rfl⟩ := hm
    have hs : SatRel core.num.U64.MAX Arena.Frontend.Olean.wordMax := by
      show _ = _
      rw [u64_max_val]
      rfl
    have hw := nat_word_eq hs hr0 (lst := lst)
    cases Result.ok_injective h
    show AErrSim ce _
    rw [StateT.run_bind]
    exact AErrSim.bind hw _

/-! ## The imports -/

/-- The handles' test, as the twin's `==`. -/
theorem nidx_beq_abs {a b : arena.handle.NIdx} {c : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok c) :
    c = (absNIdx a == absNIdx b) := by
  rw [nidx_eq2 a b c trivial trivial h]
  by_cases hab : a = b
  · subst hab; simp
  · have : absNIdx a ≠ absNIdx b := fun he => hab (absNIdx_inj he)
    simp [hab, this]

/-- **`import_rec_beq` is `==` on `ImportF`.** -/
theorem import_rec_beq_eq {a b : frontend.olean.spec.ImportF arena.handle.NIdx} {c : Bool}
    (h : frontend.olean.spec.import_rec_beq a b = ok c) :
    c = (absImportF absNIdx a == absImportF absNIdx b) := by
  rw [frontend.olean.spec.import_rec_beq] at h
  peel h as b1, hb1
  have e := nidx_beq_abs hb1
  show c = ((absNIdx a.module == absNIdx b.module) && a.import_all == b.import_all &&
    a.is_exported == b.is_exported && a.is_meta == b.is_meta)
  rw [← e]
  cases b1 with
  | false =>
    rw [ite_eq_right Bool.false_ne_true] at h
    cases Result.ok_injective h
    rfl
  | true =>
    rw [ite_eq_left rfl] at h
    split at h
    · rename_i h1
      split at h
      · rename_i h2
        cases Result.ok_injective h
        simp [h1, h2, beq_eq_decide]
      · rename_i h2
        cases Result.ok_injective h
        simp [h1, h2]
    · rename_i h1
      cases Result.ok_injective h
      simp [h1]

/-- **`imports_beq` is `==` on the twin's arrays.** -/
theorem imports_beq_eq {a b : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {c : Bool} (h : frontend.olean.spec.imports_beq a b = ok c) :
    c = ((a.val.map (absImportF absNIdx)).toArray == (b.val.map (absImportF absNIdx)).toArray) := by
  rw [frontend.olean.spec.imports_beq] at h
  rw [List.beq_toArray]
  split at h
  · rename_i hne
    cases Result.ok_injective h
    have hl : a.val.length ≠ b.val.length := by
      intro he
      have : alloc.vec.Vec.len a = alloc.vec.Vec.len b := UScalar.eq_of_val_eq (by simp only [alloc.vec.Vec.len_val]; exact he)
      simp [this] at hne
    symm
    rw [Bool.eq_false_iff]
    intro he
    exact hl (by simpa using List.length_eq_of_beq he)
  · rename_i he
    have hl : a.val.length = b.val.length := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at he
      have := congrArg UScalar.val he
      simpa only [alloc.vec.Vec.len_val] using this
    have aux : ∀ (k : Nat) (i : Std.Usize) (c : Bool), a.val.length - i.val ≤ k →
        frontend.olean.spec.imports_beq_loop a b i = ok c →
        c = ((a.val.drop i.val).map (absImportF absNIdx) ==
          (b.val.drop i.val).map (absImportF absNIdx)) := by
      intro k
      induction k with
      | zero =>
        intro i c hk h
        rw [frontend.olean.spec.imports_beq_loop, ite_eq_right (by scalar_tac)] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
        rfl
      | succ k ih =>
        intro i c hk h
        rw [frontend.olean.spec.imports_beq_loop] at h
        by_cases hi : i < alloc.vec.Vec.len a
        · rw [ite_eq_left hi] at h
          have hlt : i.val < a.val.length := by scalar_tac
          have hlt2 : i.val < b.val.length := by omega
          peel h as x, hx
          peel h as y, hy
          peel h as b1, hb1
          have ex := ConRon.Refine.ExprOps.vec_index_getElem? hx
          have ey := ConRon.Refine.ExprOps.vec_index_getElem? hy
          rw [List.getElem?_eq_getElem hlt] at ex
          rw [List.getElem?_eq_getElem hlt2] at ey
          rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hlt2, Option.some.inj ex,
            Option.some.inj ey, List.map_cons, List.map_cons, List.cons_beq_cons,
            ← import_rec_beq_eq hb1]
          cases b1 with
          | false =>
            rw [ite_eq_right Bool.false_ne_true] at h
            cases Result.ok_injective h
            rfl
          | true =>
            rw [ite_eq_left rfl] at h
            peel h as i2, hi2
            have hiv : i2.val = i.val + 1 := uscalar_add_eq hi2
            rw [Bool.true_and, ih i2 c (by omega) h, hiv]
        · rw [ite_eq_right hi] at h
          cases Result.ok_injective h
          rw [List.drop_eq_nil_of_le (by scalar_tac), List.drop_eq_nil_of_le (by scalar_tac)]
          rfl
    simpa using aux _ 0#usize c (Nat.le_refl _) h

/-- A stored constant's statement, as the twin's. -/
def absStmt (s : frontend.olean.spec.StmtRec) : Arena.Frontend.Olean.StmtRec :=
  ⟨absNIdx s.name, s.level_params.val.map absNIdx, absEIdx s.ty⟩

/-- **`c_entry_stmt` is `entryStmt`.** -/
theorem c_entry_stmt_eq {c : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {c' : CEntryF NIdx EIdx} {RN : NatRel} (hc : EntryRel absNIdx absEIdx RN c c') {s}
    (h : frontend.olean.spec.c_entry_stmt c = ok s) :
    absStmt s = Arena.Frontend.Olean.entryStmt c' := by
  rw [frontend.olean.spec.c_entry_stmt] at h
  peel h as n, hn
  peel h as v, hv
  peel h as e, he
  cases Result.ok_injective h
  obtain ⟨n', l', ty', k'⟩ := c'
  obtain ⟨rfl, rfl, rfl, -⟩ := hc
  simp [absStmt, Arena.Frontend.Olean.entryStmt, nidx_dup2_ok hn, eidx_dup2_ok he,
    nidx_vec_dup_val hv]


/-! ## The name table -/

/-- The second half of `constNamesGo`'s test of an entry: entry `n` names the constant
whose name the pointer `v` is: the same object, or the same name read. -/
def goSame (pk : Arena.Frontend.Olean.OleanPins) (r : ConLeche.Frontend.Olean.Region) (n : Nat)
    (v : UInt64) (a : NIdx) : AM Bool :=
  if (r.loc v == some n) = true then pure true
  else do
    match ← Arena.Frontend.Olean.nameP pk r v with
    | none => pure false
    | some b => pure (b == a)

/-- **`name_entry_agrees` is `constNamesGo`'s test.** -/
theorem name_entry_agrees_refines {pk bs r pers st lst} {n v : Std.U64} {a : arena.handle.NIdx}
    (hr : RegionFits bs r) :
    CS pers (· = ·) st lst
      (frontend.olean.spec.name_entry_agrees pk pers st.store bs r n v a)
      (goSame (absPins pk) (absRegion bs r) n.val (absWord v) (absNIdx a)) := by
  intro hrel hinv o s' h
  rw [frontend.olean.spec.name_entry_agrees] at h
  peel h as ol, hol
  have eL := region_loc_eq bs hol
  peel h as same, hsame
  have es : same = ((absRegion bs r).loc (absWord v) == some n.val) := by
    rw [← eL]
    cases ol with
    | none => exact (Result.ok_injective hsame).symm
    | some l =>
      cases Result.ok_injective hsame
      by_cases hln : l = n
      · subst hln; simp
      · have : l.val ≠ n.val := fun he => hln (UScalar.eq_of_val_eq he)
        simp [hln, this]
  rw [goSame, ← es]
  cases same with
  | true =>
    rw [ite_eq_left rfl] at h ⊢
    cases Result.ok_injective h
    exact ⟨true, lst, rfl, rfl, hrel, hinv⟩
  | false =>
    rw [ite_eq_right Bool.false_ne_true] at h ⊢
    peel h as p, hp
    obtain ⟨r1, ar1⟩ := p
    have hn := name_p_refines (pk := pk) (v := v) hr hrel hinv r1 ar1 hp
    cases r1 with
    | Ok b =>
      obtain ⟨b', lst1, hx, hR, rel, inv⟩ := hn
      cases hR
      rw [am_bind_ok hx]
      peel h as b1, hb1
      cases Result.ok_injective h
      exact ⟨_, lst1, rfl, nidx_beq_abs hb1, rel, inv⟩
    | Err re =>
      cases re with
      | Bad =>
        obtain ⟨lst1, hx, rel, inv⟩ := hn
        cases Result.ok_injective h
        rw [am_bind_ok hx]
        exact ⟨false, lst1, rfl, rfl, rel, inv⟩
      | Err e =>
        cases Result.ok_injective h
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hn _

/-- One entry of `constNamesGo`, with `K` the rest of the walk. -/
def goStep (pk : Arena.Frontend.Olean.OleanPins) (r : ConLeche.Frontend.Olean.Region) (n c : Nat)
    (seen : _root_.Std.HashSet NIdx) (K : _root_.Std.HashSet NIdx → AM Bool) : AM Bool :=
  match ConLeche.Frontend.Olean.constSkel r c with
  | none => pure false
  | some sk => do
    match ← Arena.Frontend.Olean.nameAt pk r n with
    | none => pure false
    | some a =>
      let sameName ← goSame pk r n sk.name a
      if !sameName then pure false
      else
        let (b, seen) := seen.containsThenInsert a
        if b then pure false else K seen

theorem constNamesGo_cons (pk : Arena.Frontend.Olean.OleanPins)
    (r : ConLeche.Frontend.Olean.Region) (n c : Nat) (ns cs : List Nat)
    (seen : _root_.Std.HashSet NIdx) :
    Arena.Frontend.Olean.constNamesGo pk r (n :: ns) (c :: cs) seen =
      goStep pk r n c seen (Arena.Frontend.Olean.constNamesGo pk r ns cs) := by
  rw [Arena.Frontend.Olean.constNamesGo, goStep]
  cases ConLeche.Frontend.Olean.constSkel r c with
  | none => rfl
  | some sk =>
    refine congrArg (Arena.Frontend.Olean.nameAt pk r n >>= ·) (funext fun o => ?_)
    cases o with
    | none => rfl
    | some a =>
      dsimp only [goSame]
      cases (r.loc sk.name == some n) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine congrArg (Arena.Frontend.Olean.nameP pk r sk.name >>= ·) (funext fun o => ?_)
        cases o <;> rfl

/-- The `seen` table of the name table: the handles, as the twin's. -/
abbrev SeenRel := SetRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx

/-- What a step of the name table claims of the twin's run `x`, whose answer `true` goes on
with `K`. -/
def StepOut (pers : arena.store.PersTier) (st' : arena.monad.AState)
    (seen1 : ron.hashmap2.HashMap2 arena.handle.NIdx Bool) (K : _root_.Std.HashSet NIdx → AM Bool)
    (x : AM Bool) (lst : AState) : core.result.Result Bool kernel.core_types.CheckError → Prop
  | .Ok false => ∃ lst1, x.run lst = .ok (false, lst1) ∧ AStateRel₀ pers st' lst1 ∧ AStateInv pers st'
  | .Ok true => ∃ se1 lst1, x.run lst = (K se1).run lst1 ∧ SeenRel seen1 se1 ∧
      AStateRel₀ pers st' lst1 ∧ AStateInv pers st'
  | .Err e => AErrSim e (x.run lst)

/-- `StepOut` only asks of `x`'s run. -/
theorem StepOut.of_run {pers st' seen1 K} {x y : AM Bool} {lst lst1 : AState} {r}
    (e : x.run lst = y.run lst1) (h : StepOut pers st' seen1 K y lst1 r) :
    StepOut pers st' seen1 K x lst r := by
  cases r with
  | Ok b =>
    cases b with
    | false => rw [StepOut] at h ⊢; rw [e]; exact h
    | true => rw [StepOut] at h ⊢; rw [e]; exact h
  | Err e' => rw [StepOut] at h ⊢; rw [e]; exact h

/-- **`const_name_step` is one entry of `constNamesGo`.** -/
theorem const_name_step_refines {pk bs r pers st lst} {n c : Std.U64} {seen seen1 s1 r1}
    {se : _root_.Std.HashSet NIdx} {K : _root_.Std.HashSet NIdx → AM Bool} (hr : RegionFits bs r)
    (hS : SeenRel seen se) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : frontend.olean.spec.const_name_step pk pers st.store bs r n c seen = ok (r1, s1, seen1)) :
    StepOut pers (withStore st s1) seen1 K
      (goStep (absPins pk) (absRegion bs r) n.val c.val se K) lst r1 := by
  rw [frontend.olean.spec.const_name_step] at h
  rw [goStep]
  peel h as o, ho
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_)
    (fun sk sk' hA hy hSk => ?_)
  · subst hA
    rw [hy]
    cases Result.ok_injective h
    exact ⟨lst, rfl, hrel, hinv⟩
  subst hA
  rw [hy]
  dsimp only at h ⊢
  rw [← hSk.«name»]
  peel h as p1, hp1
  obtain ⟨r2, ar1⟩ := p1
  have hn := name_at_refines (pk := pk) hr _ n st lst (Nat.lt_succ_self _) hrel hinv r2 ar1 hp1
  cases r2 with
  | Err re =>
    cases re with
    | Bad =>
      obtain ⟨lst1, hx, rel, inv⟩ := hn
      cases Result.ok_injective h
      rw [StepOut, am_bind_ok hx]
      exact ⟨lst1, rfl, rel, inv⟩
    | Err e =>
      cases Result.ok_injective h
      rw [StepOut, StateT.run_bind]
      exact AErrSim.bind hn _
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, rel1, inv1⟩ := hn
    cases hR
    refine StepOut.of_run (am_bind_ok hx) ?_
    dsimp only
    peel h as p2, hp2
    obtain ⟨r3, ar2⟩ := p2
    have hE := name_entry_agrees_refines (pk := pk) (n := n) (v := sk.name) (a := a)
      (st := withStore st ar1) hr rel1 inv1 r3 ar2 hp2
    cases r3 with
    | Err e =>
      cases Result.ok_injective h
      rw [StepOut, StateT.run_bind]
      exact AErrSim.bind hE _
    | Ok bb =>
      obtain ⟨bb', lst2, hx2, hR2, rel2, inv2⟩ := hE
      cases hR2
      refine StepOut.of_run (am_bind_ok hx2) ?_
      cases bb with
      | false =>
        cases Result.ok_injective h
        rw [StepOut]
        exact ⟨lst2, rfl, rel2, inv2⟩
      | true =>
        have h : (do
            let b1 ← ron.hashmap2.HashMap2.contains_key
              arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
              arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 seen a
            if b1 = true then ok (core.result.Result.Ok false, ar2, seen)
            else do
              let (_, seen1) ← ron.hashmap2.HashMap2.insert
                arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
                arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 seen a true
              ok (core.result.Result.Ok true, ar2, seen1)) = ok (r1, s1, seen1) := h
        have hsp : se.containsThenInsert (absNIdx a) =
            (se.contains (absNIdx a), se.insert (absNIdx a)) :=
          Prod.ext _root_.Std.HashSet.containsThenInsert_fst
            _root_.Std.HashSet.containsThenInsert_snd
        rw [ite_eq_right (by decide), hsp]
        dsimp only
        peel h as b1, hb1
        rw [← SetRel.contains_key nidx_eq2 hS hb1]
        cases b1 with
        | true =>
          rw [ite_eq_left rfl] at h
          cases Result.ok_injective h
          rw [StepOut]
          exact ⟨lst2, rfl, rel2, inv2⟩
        | false =>
          rw [ite_eq_right Bool.false_ne_true] at h
          peel h as p3, hp3
          obtain ⟨old, seen2⟩ := p3
          cases Result.ok_injective h
          rw [StepOut]
          exact ⟨se.insert (absNIdx a), lst2, rfl,
            SetRel.insert nidx_eq2 absNIdx_inj hS hp3, rel2, inv2⟩

/-- **`const_names_go`'s loop is `constNamesGo`** on what is left of the two lists. -/
theorem const_names_go_loop_refines {pk bs r pers} {ns cs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) (hlen : ns.val.length = cs.val.length) :
    ∀ (k : Nat) (i : Std.Usize) (st : arena.monad.AState) (lst : AState) seen se r1 s1 seen1,
      ns.val.length - i.val ≤ k → SeenRel seen se → AStateRel₀ pers st lst → AStateInv pers st →
      frontend.olean.spec.const_names_go_loop pk pers st.store bs r ns cs seen i =
        ok (r1, s1, seen1) →
      match r1 with
      | .Ok b => ∃ lst1,
          (Arena.Frontend.Olean.constNamesGo (absPins pk) (absRegion bs r)
            ((ns.val.drop i.val).map (·.val)) ((cs.val.drop i.val).map (·.val)) se).run lst =
              .ok (b, lst1) ∧
          AStateRel₀ pers (withStore st s1) lst1 ∧ AStateInv pers (withStore st s1)
      | .Err e => AErrSim e ((Arena.Frontend.Olean.constNamesGo (absPins pk) (absRegion bs r)
            ((ns.val.drop i.val).map (·.val)) ((cs.val.drop i.val).map (·.val)) se).run lst) := by
  intro k
  induction k with
  | zero =>
    intro i st lst seen se r1 s1 seen1 hk _ hrel hinv h
    rw [frontend.olean.spec.const_names_go_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    exact ⟨lst, rfl, hrel, hinv⟩
  | succ k ih =>
    intro i st lst seen se r1 s1 seen1 hk hS hrel hinv h
    rw [frontend.olean.spec.const_names_go_loop] at h
    by_cases hi : i < alloc.vec.Vec.len ns
    · rw [ite_eq_left hi] at h
      have hlt : i.val < ns.val.length := by scalar_tac
      have hlt2 : i.val < cs.val.length := by omega
      peel h as n, hn
      peel h as c, hc
      peel h as p, hp
      obtain ⟨r2, ar1, seen2⟩ := p
      have en := ConRon.Refine.ExprOps.vec_index_getElem? hn
      have ec := ConRon.Refine.ExprOps.vec_index_getElem? hc
      rw [List.getElem?_eq_getElem hlt] at en
      rw [List.getElem?_eq_getElem hlt2] at ec
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hlt2, Option.some.inj en,
        Option.some.inj ec, List.map_cons, List.map_cons, constNamesGo_cons]
      have hO := const_name_step_refines (se := se)
        (K := Arena.Frontend.Olean.constNamesGo (absPins pk) (absRegion bs r)
          ((ns.val.drop (i.val + 1)).map (·.val)) ((cs.val.drop (i.val + 1)).map (·.val)))
        hr hS hrel hinv hp
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        exact hO
      | Ok b =>
        cases b with
        | false =>
          cases Result.ok_injective h
          exact hO
        | true =>
          obtain ⟨se1, lst1, hrun, hS1, rel1, inv1⟩ := hO
          peel h as i4, hi4
          have hiv : i4.val = i.val + 1 := uscalar_add_eq hi4
          have hI := ih i4 (withStore st ar1) lst1 seen2 se1 r1 s1 seen1 (by omega) hS1 rel1 inv1 h
          rw [hiv] at hI
          rw [hrun]
          exact hI
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac), List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨lst, rfl, hrel, hinv⟩

/-- **`const_names_ok` is `constNamesOk`.** -/
theorem const_names_ok_refines {pk bs r pers st lst} {root : Std.U64} (hr : RegionFits bs r) :
    CS pers (· = ·) st lst (frontend.olean.spec.const_names_ok pk pers st.store bs r root)
      (Arena.Frontend.Olean.constNamesOk (absPins pk) (absRegion bs r) (absWord root)) := by
  rw [frontend.olean.spec.const_names_ok, Arena.Frontend.Olean.constNamesOk]
  refine CS.pure_step fun o ho => ?_
  rw [← region_loc_eq bs ho]
  cases o with
  | none => exact CS.pure rfl
  | some g =>
    dsimp only [locOf, Option.map_some]
    refine CS.pure_step fun b hb => ?_
    rw [← (ctor_at bs 0 5 hb)]
    cases b with
    | false =>
      rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
      exact CS.pure rfl
    | true =>
      rw [ite_eq_left rfl, ite_eq_left rfl]
      refine CS.pure_step fun i hi => CS.pure_step fun o1 ho1 => ?_
      have e1 := region_obj_array_eq hr ho1
      rw [← (show (absRegion bs r).fld g.val 1 = absWord i from fld_1 hi), ] at e1
      rw [← e1]
      cases o1 with
      | none => exact CS.pure rfl
      | some v =>
        refine CS.pure_step fun i1 hi1 => CS.pure_step fun o2 ho2 => ?_
        have e2 := region_obj_array_eq hr ho2
        rw [← (show (absRegion bs r).fld g.val 2 = absWord i1 from fld_2 hi1)] at e2
        rw [← e2]
        cases o2 with
        | none => exact CS.pure rfl
        | some v1 =>
          simp only [Option.map_some]
          by_cases hl : v.val.length = v1.val.length
          · have hle : alloc.vec.Vec.len v = alloc.vec.Vec.len v1 :=
              UScalar.eq_of_val_eq (by simp only [alloc.vec.Vec.len_val]; exact hl)
            have hs : (absLocs v).size = (absLocs v1).size := by simp [absLocs, hl]
            rw [ite_eq_right (by simp [hle]), ite_eq_left (by simp [hs])]
            refine CS.pure_step fun seen hseen => ?_
            intro hrel hinv o s' h
            peel h as p, hp
            obtain ⟨r1, ar1, sn⟩ := p
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
            rw [frontend.olean.spec.const_names_go] at hp
            have hG := const_names_go_loop_refines hr hl _ 0#usize st lst seen
              (_root_.Std.HashSet.emptyWithCapacity (absLocs v).size) r1 ar1 sn (Nat.le_refl _)
              (SetRel.with_capacity hseen) hrel hinv hp
            have t0 : (0#usize : Std.Usize).val = 0 := by decide
            rw [t0, List.drop_zero, List.drop_zero] at hG
            rw [show (absLocs v).toList = v.val.map (·.val) by simp [absLocs],
              show (absLocs v1).toList = v1.val.map (·.val) by simp [absLocs]]
            cases r1 with
            | Ok b =>
              obtain ⟨lst1, hrun, rel, inv⟩ := hG
              exact ⟨b, lst1, hrun, rfl, rel, inv⟩
            | Err e => exact hG
          · have hne : alloc.vec.Vec.len v ≠ alloc.vec.Vec.len v1 := fun he => hl (by
              have := congrArg UScalar.val he
              simpa only [alloc.vec.Vec.len_val] using this)
            have hs : (absLocs v).size ≠ (absLocs v1).size := by simp [absLocs, hl]
            rw [ite_eq_left (by simp [hne]), ite_eq_right (by simp [hs])]
            exact CS.pure rfl

end ConRon.Refine2.Frontend.Olean

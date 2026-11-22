/-
# `ConRon.Refine2.Frontend.Olean.PartNames` — a part's name positions

**Task #166, Theorem 2.**  `reads.rs`'s `name_position`, `name_positions_go`, `imports_named`,
`distinct_go`, `name_positions_at` against the twin's `namePosition`/`namePositionsAt` (`RS`),
`view.rs`'s `read_name_positions` against `readNamePositions` (`RS`), and `files.rs`'s
`names_of`, `read_part_names_at`, `read_part_names`, which reach a file read, against
`namesOf`/`readPartNamesAt`/`readPartNames` (their accept, `AS`).
-/
import ConRon.Refine2.Frontend.Olean.NamePos
import ConRon.Refine2.Frontend.Olean.FilesRead

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.reads (name_position name_positions_go name_positions_go_loop imports_named
  imports_named_loop distinct_go distinct_go_loop name_positions_at c_kind_tag c_kind_skipped)
open frontend.olean.view (read_name_positions view_bytes view_region_of mod_files_view_region)
open frontend.olean.files (names_of read_part_names_at read_part_names read_files_at find_module)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConLeche.Frontend.Olean (CKindF)
open Arena.Frontend.Olean (namePosition namePositionsAt readNamePositions namesOf readPartNamesAt
  readPartNames nameP)

/-! ## A kind's tag and filter -/

/-- **`c_kind_tag` is `CKindF.tag`.** -/
theorem c_kind_tag_eq {N N' E E' : Type} {AN : N → N'} {AE : E → E'} {RN : NatRel}
    {k : frontend.olean.spec.CKindF N E} {k' : CKindF N' E'} (hk : KindRel AN AE RN k k')
    {t : Std.U64} (h : c_kind_tag k = ok t) : t.val = k'.tag := by
  rw [frontend.olean.reads.c_kind_tag.eq_def] at h
  cases k <;> cases k' <;> try exact (hk : False).elim
  all_goals (cases Result.ok_injective h; rfl)

/-- **`c_kind_skipped` is `CKindF.skipped`.** -/
theorem c_kind_skipped_eq {N N' E E' : Type} {AN : N → N'} {AE : E → E'} {RN : NatRel}
    {k : frontend.olean.spec.CKindF N E} {k' : CKindF N' E'} (hk : KindRel AN AE RN k k')
    {b : Bool} (h : c_kind_skipped k = ok b) : b = k'.skipped := by
  rw [frontend.olean.reads.c_kind_skipped.eq_def] at h
  cases k <;> cases k' <;> try exact (hk : False).elim
  case Ax.ax u u' => cases (hk : u = u'); exact (Result.ok_injective h).symm
  case Defn.defn v hh s v' h' s' =>
    obtain ⟨-, -, rfl, hw⟩ := hk
    simp only [lift, bind_ok] at h
    peel h as b1, hb1
    cases Result.ok_injective h
    have hv : (Std.Array.to_slice frontend.olean.reads.c_kind_skipped.S_SAFE).val
        = [115#u32, 97#u32, 102#u32, 101#u32] := by
      unfold frontend.olean.reads.c_kind_skipped.S_SAFE; rfl
    have e := cps_beq_str hw (by rw [hv]; decide) hb1
    rw [hv] at e
    have e' : (b1 = true) ↔ ConRon.Refine.absString s = "safe" := e.trans (by rfl)
    show decide ¬ b1 = true = (ConRon.Refine.absString s != "safe")
    cases b1 <;> simp [e'.symm]
  case Thm.thm v a v' a' => exact (Result.ok_injective h).symm
  case Opaq.opaq v u v' u' =>
    obtain ⟨-, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Quot.quot s s' => exact (Result.ok_injective h).symm
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hk
    exact (Result.ok_injective h).symm
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨-, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm

/-! ## One position, all positions -/

/-- **`name_position` is `namePosition`.** -/
theorem name_position_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNamePosition) st lst (name_position pk pers st.store bs r c)
      (namePosition (absPins pk) (absRegion bs r) c.val) := by
  rw [name_position, namePosition]
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_)
    (fun s s' hA hy hS => ?_)
  · subst hA; rw [hy]; exact RS.none
  · subst hA
    rw [hy]
    dsimp only
    rw [← hS.«name»]
    refine RS.bind_of (name_p_refines hr) (fun _ _ => rfl) rfl fun a b s1 lst1 hR => ?_
    refine RS.pure_step fun i hi => RS.pure_step fun bb hbb => ?_
    cases hR
    refine RS.some ?_
    show _ = absNamePosition _
    rw [absNamePosition, c_kind_tag_eq hS.kind hi, c_kind_skipped_eq hS.kind hbb]

/-- **`name_positions_go` is `consts.mapM namePosition`**, at `OptionT AM`. -/
theorem name_positions_go_refines {pk bs r pers} {cs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r)
    (st lst) :
    RS pers (fun v l => List.Forall₂ (EqA absNamePosition) v.val l) st lst
      (name_positions_go pk pers st.store bs r cs)
      ((cs.val.map (·.val)).mapM (m := OptionT AM) fun c =>
        OptionT.mk (namePosition (absPins pk) (absRegion bs r) c)) := by
  rw [name_positions_go]
  refine RS.vec_map (R := EqA absNamePosition)
    (loop := fun ar out i => name_positions_go_loop pk pers ar bs r cs out i)
    (forall₂_of_map (A := fun v : Std.U64 => v.val) cs.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show name_positions_go_loop pk pers ar bs r cs out i = _
    rw [name_positions_go_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (name_positions_go_loop pk pers st.store bs r cs out i) _
    rw [name_positions_go_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (name_position_refines hr) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`imports_named` is `imports.mapM (ImportF.mapM nameP)`**, at `OptionT AM`. -/
theorem imports_named_refines {pk bs r pers} {imps : alloc.vec.Vec (frontend.olean.spec.ImportF Std.U64)}
    (hr : RegionFits bs r) (st lst) :
    RS pers (fun v l => List.Forall₂ (EqA (absImportF absNIdx)) v.val l) st lst
      (imports_named pk pers st.store bs r imps)
      ((imps.val.map (absImportF absWord)).mapM (m := OptionT AM) fun i =>
        i.mapM (m := OptionT AM) fun v => OptionT.mk (nameP (absPins pk) (absRegion bs r) v)) := by
  have hp := name_p_read_rel (pk := pk) (pers := pers) hr
  rw [imports_named]
  refine RS.vec_map (R := EqA (absImportF absNIdx))
    (loop := fun ar out i => imports_named_loop pk pers ar bs r imps out i)
    (forall₂_of_map (A := absImportF absWord) imps.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show imports_named_loop pk pers ar bs r imps out i = _
    rw [imports_named_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (imports_named_loop pk pers st.store bs r imps out i) _
    rw [imports_named_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (import_map_refines hp st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-! ## The names are distinct -/

/-- **`distinct_go`'s loop is `distinctGo`** on what is left of the positions. -/
theorem distinct_go_loop_eq {cs : alloc.vec.Vec frontend.olean.reads.NamePosition} :
    ∀ (k : Nat) (i : Std.Usize) seen (se : _root_.Std.HashSet NIdx) (b : Bool),
      cs.val.length - i.val ≤ k → SeenRel seen se → distinct_go_loop cs seen i = ok b →
      b = ConLeche.Frontend.Olean.distinctGo ((cs.val.drop i.val).map fun p => absNIdx p.name) se := by
  intro k
  induction k with
  | zero =>
    intro i seen se b hk _ h
    rw [distinct_go_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i seen se b hk hS h
    rw [distinct_go_loop] at h
    by_cases hi : i < alloc.vec.Vec.len cs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      peel h as np, hnp
      have en := ConRon.Refine.ExprOps.vec_index_getElem? hnp
      rw [List.getElem?_eq_getElem hlt] at en
      rw [List.drop_eq_getElem_cons hlt, Option.some.inj en, List.map_cons,
        ConLeche.Frontend.Olean.distinctGo]
      have hsp : se.containsThenInsert (absNIdx np.name) =
          (se.contains (absNIdx np.name), se.insert (absNIdx np.name)) :=
        Prod.ext _root_.Std.HashSet.containsThenInsert_fst _root_.Std.HashSet.containsThenInsert_snd
      rw [hsp]
      dsimp only
      peel h as b1, hb1
      rw [← SetRel.contains_key nidx_eq2 hS hb1]
      cases b1 with
      | true =>
        rw [ite_eq_left rfl] at h
        cases Result.ok_injective h
        rfl
      | false =>
        rw [ite_eq_right Bool.false_ne_true] at h
        peel h as n, hn
        rw [nidx_dup2_ok hn] at h
        peel h as p, hp
        obtain ⟨old, seen1⟩ := p
        peel h as i2, hi2
        have hiv : i2.val = i.val + 1 := uscalar_add_eq hi2
        have hI := ih i2 seen1 _ b (by omega) (SetRel.insert nidx_eq2 absNIdx_inj hS hp) h
        rw [hiv] at hI
        rw [hI]
        rfl
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      rfl

/-- **`distinct_go` is `distinctGo`**, from any empty set. -/
theorem distinct_go_eq {cs : alloc.vec.Vec frontend.olean.reads.NamePosition} {b : Bool} (n : Nat)
    (h : distinct_go cs = ok b) :
    b = ConLeche.Frontend.Olean.distinctGo (cs.val.map fun p => absNIdx p.name)
      (_root_.Std.HashSet.emptyWithCapacity n) := by
  rw [distinct_go] at h
  peel h as s, hs
  have := distinct_go_loop_eq _ 0#usize s _ b (Nat.le_refl _)
    (SetRel.with_capacity (n := n) (hI := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
      (A := absNIdx) hs) h
  simpa using this

/-! ## The name positions of a part -/

/-- **`name_positions_at` is `namePositionsAt`.** -/
theorem name_positions_at_refines {pk bs r pers st lst} {root : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNamePositions) st lst (name_positions_at pk pers st.store bs r root)
      (namePositionsAt (absPins pk) (absRegion bs r) (absWord root)) := by
  rw [name_positions_at, namePositionsAt]
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (module_skel_eq hr ho) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
  · subst hA; rw [hy]; exact RS.none
  · subst hA
    rw [hy]
    dsimp only
    rw [← hS.imports, ← hS.consts]
    refine RS.bindT (imports_named_refines hr st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT (name_positions_go_refines hr _ lst1) (fun _ _ => by rfl)
        fun a2 b2 s2 lst2 hR2 => RS.pure_step fun bb hbb => ?_
    have e2 : b2 = a2.val.map absNamePosition := (forall₂_eqA hR2).symm
    have e1 : b = a.val.map (absImportF absNIdx) := (forall₂_eqA hR).symm
    subst e1 e2
    have ed := distinct_go_eq (a2.val.map absNamePosition).length hbb
    rw [List.map_map] at ⊢
    have ef : ((fun x : Arena.Frontend.Olean.NamePosition => x.name) ∘ absNamePosition) =
        fun p => absNIdx p.name := rfl
    rw [ef, ← ed]
    cases bb with
    | true =>
      rw [ite_eq_left rfl]
      refine RS.some ?_
      show _ = absNamePositions _
      rw [absNamePositions, absModHeader, hS.isModule]
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      exact RS.none

/-- **`read_name_positions` is `readNamePositions`.** -/
theorem read_name_positions_refines {pk pers st lst} {f : frontend.olean.view.ModFiles}
    {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f')
    {level : frontend.olean.view.OLeanLevel} :
    RS pers (EqA absNamePositions) st lst (read_name_positions pk pers st.store f level)
      (readNamePositions (absPins pk) f' (absLevel level)) := by
  rw [read_name_positions, readNamePositions]
  refine RS.pure_step fun o ho => ?_
  have hv := mod_files_view_region_eq hf ho
  cases o with
  | none =>
    rw [show f'.viewRegion (absLevel level) = none from hv]
    exact RS.none
  | some p =>
    obtain ⟨vb, a⟩ := p
    dsimp only
    refine RS.pure_step fun bs hbs => RS.pure_step fun r hr => ?_
    obtain ⟨e, hfit⟩ := hv bs r hbs hr
    rw [e]
    exact name_positions_at_refines hfit

/-! ## Off a module's files -/

/-- **`names_of`'s accept is `namesOf`**, whatever name the twin's failure would cite. -/
theorem names_of_refines {pk pers st lst} {m : arena.handle.NIdx} {n : ConLeche.Name}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f')
    {level : frontend.olean.view.OLeanLevel} :
    AS pers (EqA absNamePositions) st lst (names_of pk pers st.store m f level)
      (namesOf (absPins pk) n f' (absLevel level)) := by
  intro hrel hinv a s' h
  rw [names_of] at h
  obtain ⟨⟨r1, s1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hR := read_name_positions_refines (pk := pk) (st := st) (lst := lst) hf (level := level)
    hrel hinv r1 s1 h1
  cases r1 with
  | Ok ps =>
    cases Result.ok_injective h2
    obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ := hR
    refine ⟨b, lst1, ?_, hb, hrel1, hinv1⟩
    rw [namesOf, am_bind_ok hx]
    rfl
  | Err re =>
    cases re with
    | Bad =>
      peel h2 as ce, -
      cases Result.ok_injective h2
    | Err e => cases Result.ok_injective h2

section files

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F}
  {fs : Arena.Frontend.Olean.OleanFs}

/-- **`read_part_names_at`'s accept is `readPartNamesAt`.** -/
theorem read_part_names_at_refines {pk pers st lst} {loc : frontend.olean.files.Located}
    {m : arena.handle.NIdx} {n : kernel.name.Name} {level : frontend.olean.view.OLeanLevel}
    (hfs : FsRel inst fsv fs) (hn : arena.env.read_name pers st.store m = ok (.Ok n)) :
    AS pers (EqA absNamePositions) st lst (read_part_names_at inst fsv pk pers st.store loc m level)
      (readPartNamesAt fs (absPins pk) (absLocated loc) (ConRon.Refine.absName n) (absLevel level)) := by
  intro hrel hinv a s' h
  rw [read_part_names_at] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok f =>
    obtain ⟨f', e1, hf⟩ := read_files_at_refines hfs hn hr
    obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ := names_of_refines (n := ConRon.Refine.absName n) hf
      hrel hinv a s' h
    refine ⟨b, lst1, ?_, hb, hrel1, hinv1⟩
    simp only [readPartNamesAt, e1, Arena.Frontend.Olean.liftE]
    exact hx

/-- The name `read_part_names_at`'s accept read. -/
theorem read_part_names_at_name {pk pers ar} {loc : frontend.olean.files.Located}
    {m : arena.handle.NIdx} {level : frontend.olean.view.OLeanLevel} {a s'}
    (h : read_part_names_at inst fsv pk pers ar loc m level = ok (.Ok a, s')) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [read_part_names_at] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok f => exact read_files_at_name hr

/-- **`read_part_names`' accept is `readPartNames`.** -/
theorem read_part_names_refines {pk pers st lst} {sp : frontend.olean.files.Roots}
    {m : arena.handle.NIdx} {level : frontend.olean.view.OLeanLevel} (hfs : FsRel inst fsv fs) :
    AS pers (EqA absNamePositions) st lst (read_part_names inst fsv pk pers st.store sp m level)
      (readPartNames fs (absPins pk) (absRoots sp) (absNIdx m) (absLevel level)) := by
  intro hrel hinv a s' h
  rw [read_part_names] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok loc =>
    obtain ⟨n, hn⟩ := read_part_names_at_name h
    have e1 := find_module_ok hfs hn hr
    obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ := read_part_names_at_refines hfs hn hrel hinv a s' h
    refine ⟨b, lst1, ?_, hb, hrel1, hinv1⟩
    show ((Arena.readName (absNIdx m)) >>= _).run lst = _
    rw [am_bind_ok (read_name_run hrel hn)]
    simp only [e1]
    exact hx

end files

end ConRon.Refine2.Frontend.Olean

/-
# `ConRon.Refine2.Frontend.Olean.FilesRead` — a module's reads, in `olean/files.rs`

**Task #142, Theorem 2.**  What the search of `Files.lean` answers, read: the header's chunks,
the imports, the files a view reads, a view.  Each reaches a file read, so each claims its
accept (`AS`, or `.ok` of the twin for a pure one).

`first_bad_view`, `missing_part`, `outside_or_escaping` carry no theorem: they only build a failure, and a failure of
a function that reads a file claims nothing.
-/
import ConRon.Refine2.Frontend.Olean.Files
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.Header

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.files
open frontend.olean.region (part_of_bytes)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine (absString absName StrWF NameWF vec_push_val)
open ConRon.Refine2.Lockstep (LSP)
open ConRon.Refine2 (AErrKind absAErrKind)
open Arena.Frontend.Olean (findModule readPartOr hdrShort readHdrBytes hdrChunkN)

/-- **`hdr_short` is `hdrShort`**, of fewer than `2 ^ 60` bytes. -/
theorem hdr_short_eq {acc : alloc.vec.Vec Std.U8} {b : Bool} (hb : acc.val.length < 2 ^ 60)
    (h : hdr_short acc = ok b) : b = hdrShort (absBytes (alloc.vec.Vec.deref acc)) := by
  rw [hdr_short] at h
  peel h as w, hw
  have ew := hdr_walk_eq (by rw [deref_val]; exact hb) hw
  rw [show frontend.olean.region.DATA_START.val = ConLeche.Frontend.Olean.dataStart from data_start_val] at ew
  rw [hdrShort, ← ew]
  cases w <;> exact (Result.ok_injective h).symm

section reads

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}

/-! ## The header -/

theorem hdr_chunk_val : HDR_CHUNK.val = hdrChunkN := by unfold HDR_CHUNK hdrChunkN; decide

/-- The loop only appends. -/
theorem read_hdr_bytes_loop_mono {p : alloc.vec.Vec Std.U32} {size : Std.U64}
    (acc : alloc.vec.Vec Std.U8) (off : Std.U64) (more : Bool) {o}
    (h : read_hdr_bytes_loop inst fsv p size acc off more = ok (.Ok o)) :
    acc.val.length ≤ o.val.length := by
  rw [read_hdr_bytes_loop] at h
  by_cases hm : more = true
  · rw [ite_eq_left hm] at h
    by_cases hlt : off < size
    · rw [ite_eq_left hlt] at h
      peel h as r, -
      cases r with
      | Err e =>
        peel h as ce, -
        cases Result.ok_injective h
      | Ok c =>
        peel h as acc1, hacc
        peel h as i, hi
        peel h as i1, hi1
        peel h as off1, hoff
        peel h as more1, -
        have hiv : i.val = size.val - off.val := ConRon.Refine.HashMap.uscalar_sub_eq hi
        have hoffv : off1.val = off.val + i1.val := ConRon.Refine.HashMap.uscalar_add_eq hoff
        have hlt' : off.val < size.val := hlt
        have hpos : 0 < i1.val := by
          by_cases hc : HDR_CHUNK < i
          · rw [ite_eq_left hc] at hi1
            cases Result.ok_injective hi1
            rw [hdr_chunk_val]
            unfold hdrChunkN
            omega
          · rw [ite_eq_right hc] at hi1
            cases Result.ok_injective hi1
            omega
        have ih := read_hdr_bytes_loop_mono acc1 off1 more1 h
        have el : acc1.val.length = acc.val.length + c.val.length := by
          rw [extend_u8_val hacc, deref_val]; simp
        omega
    · rw [ite_eq_right hlt] at h
      cases Result.ok_injective h
      exact Nat.le_refl _
  · rw [ite_eq_right hm] at h
    cases Result.ok_injective h
    exact Nat.le_refl _
termination_by (if more then size.val + 1 else 0) - off.val
decreasing_by
  repeat' split
  all_goals omega

/-- **`read_hdr_bytes`'s loop is `readHdrBytes`**, what it answers being under the size limit. -/
theorem read_hdr_bytes_loop_ok {p : alloc.vec.Vec Std.U32} {q : System.FilePath} {size : Std.U64}
    (hfs : FsRel inst fsv fs) (hrel : PathRel p q)
    (acc : alloc.vec.Vec Std.U8) (off : Std.U64) (more : Bool) {o} (hb : o.val.length < 2 ^ 60)
    (h : read_hdr_bytes_loop inst fsv p size acc off more = ok (.Ok o)) :
    (if more then readHdrBytes fs q size.val off.val (absBytes (alloc.vec.Vec.deref acc))
      else .ok (absBytes (alloc.vec.Vec.deref acc))) = .ok (absBytes (alloc.vec.Vec.deref o)) := by
  rw [read_hdr_bytes_loop] at h
  cases more with
  | false =>
    cases Result.ok_injective h
    rfl
  | true =>
    simp only [↓reduceIte] at h ⊢
    rw [readHdrBytes]
    by_cases hlt : off < size
    · rw [ite_eq_left hlt] at h
      have hlt' : off.val < size.val := hlt
      rw [dite_eq_left hlt']
      peel h as r, hr
      cases r with
      | Err e =>
        peel h as ce, -
        cases Result.ok_injective h
      | Ok c =>
        have e1 := hfs.readRange hrel off HDR_CHUNK c hr
        rw [hdr_chunk_val] at e1
        rw [e1]
        dsimp only at h
        peel h as acc1, hacc
        peel h as i, hi
        peel h as i1, hi1
        peel h as off1, hoff
        peel h as more1, hm
        have eS := hdr_short_eq (Nat.lt_of_le_of_lt (read_hdr_bytes_loop_mono _ _ _ h) hb) hm
        have ea : absBytes (alloc.vec.Vec.deref acc) ++ absBytes (alloc.vec.Vec.deref c) =
            absBytes (alloc.vec.Vec.deref acc1) :=
          (join_bytes (extend_u8_val hacc ▸ (by rw [deref_val]))).symm
        have hiv : i.val = size.val - off.val := ConRon.Refine.HashMap.uscalar_sub_eq hi
        have hoffv : off1.val = off.val + i1.val := ConRon.Refine.HashMap.uscalar_add_eq hoff
        have hmin : off1.val = min (off.val + hdrChunkN) size.val := by
          by_cases hc : HDR_CHUNK < i
          · rw [ite_eq_left hc] at hi1
            cases Result.ok_injective hi1
            have : HDR_CHUNK.val < i.val := hc
            rw [hdr_chunk_val] at this
            rw [hoffv, hdr_chunk_val]; omega
          · rw [ite_eq_right hc] at hi1
            cases Result.ok_injective hi1
            have : ¬ HDR_CHUNK.val < i.val := hc
            rw [hdr_chunk_val] at this
            omega
        have hpos : off.val < off1.val := by
          rw [hmin]; unfold hdrChunkN; omega
        have ih := read_hdr_bytes_loop_ok hfs hrel acc1 off1 more1 hb h
        show (let acc := _; if hdrShort acc = true then _ else _) = _
        dsimp only
        rw [ea, ← eS, ← hmin]
        exact ih
    · rw [ite_eq_right hlt] at h
      have hlt' : ¬ off.val < size.val := hlt
      rw [dite_eq_right hlt']
      cases Result.ok_injective h
      rfl
termination_by (if more then size.val + 1 else 0) - off.val
decreasing_by
  repeat' split
  all_goals omega

/-- **`read_hdr_bytes` is `readHdrBytes`**, from the start of the file. -/
theorem read_hdr_bytes_ok {p : alloc.vec.Vec Std.U32} {q : System.FilePath} {size : Std.U64} {o}
    (hfs : FsRel inst fsv fs) (hrel : PathRel p q) (hb : o.val.length < 2 ^ 60)
    (h : read_hdr_bytes inst fsv p size = ok (.Ok o)) :
    readHdrBytes fs q size.val 0 .empty = .ok (absBytes (alloc.vec.Vec.deref o)) := by
  rw [read_hdr_bytes] at h
  have := read_hdr_bytes_loop_ok hfs hrel _ _ _ hb h
  have e0 : absBytes (alloc.vec.Vec.deref (alloc.vec.Vec.new Std.U8)) = ByteArray.empty := by
    apply ByteArray.ext
    simp only [absBytes, deref_val]
    rfl
  rw [e0] at this
  exact this

/-! ## The name read back -/

theorem read_name_run {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (hrel : AStateRel₀ pers st lst) {m : arena.handle.NIdx} {n : kernel.name.Name}
    (hn : arena.env.read_name pers st.store m = ok (.Ok n)) :
    (Arena.readName (absNIdx m)).run lst = .ok (absName n, lst) := by
  have h := ConRon.Refine2.Frontend.env_read_name_abs hrel.store hn
  show (match denoteN lst.store.ns (absNIdx m) with
    | some x => (pure x : AM _)
    | none => fail _).run lst = _
  cases hd : denoteN lst.store.ns (absNIdx m) with
  | none =>
    rw [hd] at h
    obtain ⟨_, he, _⟩ := h
    cases he
  | some x =>
    rw [hd] at h
    obtain ⟨y, he, hy⟩ := h
    cases he
    rw [← hy]
    rfl

/-! ## The imports -/

/-- The name `read_imports_at`'s accept read. -/
theorem read_imports_at_name {pk pers ar loc m a s'}
    (h : read_imports_at inst fsv pk pers ar loc m = ok (.Ok a, s')) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [read_imports_at] at h
  peel h as s0, -
  peel h as v, -
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p => exact mod_file_name hr

/-- **`read_imports_at`'s accept is the twin's `readImportsAt`.** -/
theorem read_imports_at_ok {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {loc : Located} {m : arena.handle.NIdx}
    {n : kernel.name.Name} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers st.store m = ok (.Ok n)) :
    AS pers (EqA absImports) st lst (read_imports_at inst fsv pk pers st.store loc m)
      (Arena.Frontend.Olean.readImportsAt fs (absPins pk) (absLocated loc) (absName n)) := by
  intro hrel hinv a s' h
  rw [read_imports_at] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean" := abs_olean_lit (by unfold read_imports_at.M; decide) hs0 hv
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrelP := pathRel_of hn hr
    rw [ev] at hrelP
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e =>
      peel h as ce, -
      cases Result.ok_injective h
    | Ok sz =>
      have e1 := hfs.fileSize hrelP sz hr1
      dsimp only at h
      peel h as r2, hr2
      cases r2 with
      | Err e =>
        dsimp only at h
        peel h as ce, -
        cases Result.ok_injective h
      | Ok acc =>
        dsimp only at h
        peel h as q3, hq3
        obtain ⟨r3, ar1⟩ := q3
        rw [hdr_fin] at hq3
        peel hq3 as r4, hr4
        have hP := part_of_bytes_eq (ConLeche.Frontend.Olean.modFile ⟨absString loc.dir⟩ (absName n) "olean").toString hr4
        cases r4 with
        | Err e =>
          cases Result.ok_injective hq3
          cases Result.ok_injective h
        | Ok pt =>
          obtain ⟨e3, hb, hfit⟩ := hP
          cases hb
          have e2 := read_hdr_bytes_ok hfs hrelP hfit.size hr2
          dsimp only at hq3
          cases r3 with
          | Err re =>
            cases re with
            | Bad =>
              peel h as ce, -
              cases Result.ok_injective h
            | Err e => cases Result.ok_injective h
          | Ok imps =>
            obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
            cases h1
            obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := imports_pre_refines (st := st) (lst := lst) (pk := pk) (b := alloc.vec.Vec.deref pt.bytes)
              (by rw [deref_val]; exact hfit.size) hrel hinv _ _ hq3
            refine ⟨b, lst1, ?_, hR, hrel1, hinv1⟩
            have hE : (Arena.Frontend.Olean.readImportsAt fs (absPins pk) (absLocated loc) (absName n)).run lst =
                ((Arena.Frontend.Olean.importsPre (absPins pk) (absBytes (alloc.vec.Vec.deref pt.bytes)) >>= fun o =>
                  match o with
                  | some imps => pure imps
                  | none => fail (Arena.Frontend.Olean.undecodable (absName n))) : AM _).run lst := by
              simp only [Arena.Frontend.Olean.readImportsAt, absLocated, e1, e2,
                Arena.Frontend.Olean.hdrFin, e3]
              rfl
            rw [hE, am_bind_ok hx]
            rfl

/-- **`module_imports`'s accept is the twin's `moduleImports`.** -/
theorem module_imports_refines {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {sp : frontend.olean.files.Roots}
    {m : arena.handle.NIdx} (hfs : FsRel inst fsv fs) :
    AS pers (EqA absImports) st lst (module_imports inst fsv pk pers st.store sp m)
      (Arena.Frontend.Olean.moduleImports fs (absPins pk) (absRoots sp) (absNIdx m)) := by
  intro hrel hinv a s' h
  rw [module_imports] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok loc =>
    dsimp only at h
    obtain ⟨n, hn⟩ := read_imports_at_name h
    have e1 := find_module_ok hfs hn hr
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := read_imports_at_ok hfs hn hrel hinv a s' h
    refine ⟨b, lst1, ?_, hR, hrel1, hinv1⟩
    show ((Arena.readName (absNIdx m)) >>= _).run lst = _
    rw [am_bind_ok (read_name_run hrel hn)]
    simp only [e1]
    exact hx

/-! ## The files of a view, on the twin's side -/

section twin
open ConLeche.Frontend.Olean (modFile ModFiles OLeanLevel Part)
open Arena.Frontend.Olean (readFilesAt pathExistsE)
variable {m : ConLeche.Name} {loc : ConLeche.Frontend.Olean.Located} {ex : Part}

theorem readFilesAt_exported
    (hE : ∀ a, readPartOr fs (modFile loc.dir m "olean") a = .ok ex) :
    readFilesAt fs loc m .exported = .ok { exported := ex } := by
  simp only [readFilesAt, Bind.bind, Except.bind, hE]
  rfl

theorem readFilesAt_classic {level : OLeanLevel} (hl : level ≠ .exported)
    (hE : ∀ a, readPartOr fs (modFile loc.dir m "olean") a = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = false)
    (hs : pathExistsE fs (modFile loc.dir m "olean.server") = .ok false)
    (hp : pathExistsE fs (modFile loc.dir m "olean.private") = .ok false) :
    readFilesAt fs loc m level = .ok { exported := ex } := by
  have hl' : (level == .exported) = false := by cases level <;> first | rfl | exact absurd rfl hl
  simp only [readFilesAt, Bind.bind, Except.bind, hE, hl', hM, hs, hp]
  rfl

theorem readFilesAt_server {s : Part}
    (hE : ∀ a, readPartOr fs (modFile loc.dir m "olean") a = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = true)
    (hS : ∀ a, readPartOr fs (modFile loc.dir m "olean.server") a = .ok s)
    (hp : pathExistsE fs (modFile loc.dir m "olean.private") = .ok true) :
    readFilesAt fs loc m .server = .ok { exported := ex, server := some s } := by
  simp only [readFilesAt, Bind.bind, Except.bind, hE, hM, hS, hp]
  rfl

theorem readFilesAt_private {s p : Part}
    (hE : ∀ a, readPartOr fs (modFile loc.dir m "olean") a = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = true)
    (hS : ∀ a, readPartOr fs (modFile loc.dir m "olean.server") a = .ok s)
    (hP : ∀ a, readPartOr fs (modFile loc.dir m "olean.private") a = .ok p) :
    readFilesAt fs loc m .private = .ok { exported := ex, server := some s, «private» := some p } := by
  simp only [readFilesAt, Bind.bind, Except.bind, hE, hM, hS, hP]
  rfl

end twin

/-! ## The files of a view -/

section files
variable {pers : arena.store.PersTier} {ar : arena.store.EStore} {m : arena.handle.NIdx}
  {n : kernel.name.Name}

/-- The twin's request for a file beside the `.olean`. -/
abbrev fileQ (dir : alloc.vec.Vec Std.U32) (n : kernel.name.Name) (e : String) : System.FilePath :=
  ConLeche.Frontend.Olean.modFile ⟨absString dir⟩ (absName n) e

theorem read_files_parts_server {l : Located} {f o} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files_parts inst fsv pers ar m l f .Server = ok (.Ok o)) :
    ∃ s, (∀ a, readPartOr fs (fileQ l.dir n "olean.server") a = .ok (absPart s)) ∧ PartFits s ∧
      Arena.Frontend.Olean.pathExistsE fs (fileQ l.dir n "olean.private") = .ok true ∧
      o = { f with server := some s, private_part := none } := by
  rw [read_files_parts] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean.server" := abs_server_lit (by unfold read_files_parts.M; decide) hs0 hv
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok s =>
    have e1 := fun a => (read_part_at_ok hfs hn hr a).1
    have hf := (read_part_at_ok hfs hn hr (fun _ => .internal "")).2
    rw [ev] at e1
    dsimp only at h
    peel h as s1, hs1
    peel h as v1, hv1
    have ev1 : absString v1 = "olean.private" :=
      abs_private_lit (by unfold read_files_parts.M_1; decide) hs1 hv1
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok b =>
      have e2 := path_exists_at_ok hfs hn hr1
      rw [ev1] at e2
      dsimp only at h
      by_cases hb : b = true
      · rw [ite_eq_left hb] at h
        cases Result.ok_injective h
        subst hb
        exact ⟨s, e1, hf, e2, rfl⟩
      · rw [ite_eq_right hb] at h
        exact absurd h (not_ok_of_err (by err_any))

theorem read_files_parts_private {l : Located} {f o} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files_parts inst fsv pers ar m l f .Private = ok (.Ok o)) :
    ∃ s p, (∀ a, readPartOr fs (fileQ l.dir n "olean.server") a = .ok (absPart s)) ∧ PartFits s ∧
      (∀ a, readPartOr fs (fileQ l.dir n "olean.private") a = .ok (absPart p)) ∧ PartFits p ∧
      o = { f with server := some s, private_part := some p } := by
  rw [read_files_parts] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean.server" := abs_server_lit (by unfold read_files_parts.M; decide) hs0 hv
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok s =>
    have e1 := fun a => (read_part_at_ok hfs hn hr a).1
    have hf := (read_part_at_ok hfs hn hr (fun _ => .internal "")).2
    rw [ev] at e1
    dsimp only at h
    peel h as s1, hs1
    peel h as v1, hv1
    have ev1 : absString v1 = "olean.private" :=
      abs_private_lit (by unfold read_files_parts.M_3; decide) hs1 hv1
    peel h as r2, hr2
    cases r2 with
    | Err e => cases Result.ok_injective h
    | Ok q =>
      have e2 := fun a => (read_part_at_ok hfs hn hr2 a).1
      have hf2 := (read_part_at_ok hfs hn hr2 (fun _ => .internal "")).2
      rw [ev1] at e2
      cases Result.ok_injective h
      exact ⟨s, q, e1, hf, e2, hf2, rfl⟩

theorem mf_rel_exported {p : frontend.olean.region.Part} (hf : PartFits p) :
    ModFilesRel { exported := p, server := none, private_part := none } { exported := absPart p } :=
  ⟨rfl, rfl, rfl, hf, by simp, by simp⟩

/-- The classic arm of `read_files_at`: both parts absent, the exported part alone. -/
theorem classic_arm {l : Located} {ex : frontend.olean.region.Part} {o : frontend.olean.view.ModFiles}
    (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : (do
      let s1 ← lift (Array.to_slice read_files_at.M_1)
      let v1 ← kernel.core_types.code_points s1
      let r1 ← path_exists_at inst fsv pers ar l m v1
      match r1 with
      | core.result.Result.Ok b1 =>
        let s2 ← lift (Array.to_slice read_files_at.M_2)
        let v2 ← kernel.core_types.code_points s2
        let r2 ← path_exists_at inst fsv pers ar l m v2
        match r2 with
        | core.result.Result.Ok b2 =>
          if b1 then
            let ce ← outside_or_escaping pers ar l m ex b2
            ok (core.result.Result.Err ce)
          else if b2 then
            let ce ← outside_or_escaping pers ar l m ex b2
            ok (core.result.Result.Err ce)
          else ok (core.result.Result.Ok ({ exported := ex, server := none, private_part := none } :
            frontend.olean.view.ModFiles))
        | core.result.Result.Err e => ok (core.result.Result.Err e)
      | core.result.Result.Err e => ok (core.result.Result.Err e) :
      Result (core.result.Result frontend.olean.view.ModFiles kernel.core_types.CheckError)) =
      ok (.Ok o)) :
    Arena.Frontend.Olean.pathExistsE fs (fileQ l.dir n "olean.server") = .ok false ∧
      Arena.Frontend.Olean.pathExistsE fs (fileQ l.dir n "olean.private") = .ok false ∧
      o = ({ exported := ex, server := none, private_part := none } : frontend.olean.view.ModFiles) := by
  peel h as s1, hs1
  peel h as v1, hv1
  have ev1 : absString v1 = "olean.server" :=
    abs_server_lit (by unfold read_files_at.M_1; decide) hs1 hv1
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok b1 =>
    have e1 := path_exists_at_ok hfs hn hr1
    rw [ev1] at e1
    dsimp only at h
    peel h as s2, hs2
    peel h as v2, hv2
    have ev2 : absString v2 = "olean.private" :=
      abs_private_lit (by unfold read_files_at.M_2; decide) hs2 hv2
    peel h as r2, hr2
    cases r2 with
    | Err e => cases Result.ok_injective h
    | Ok b2 =>
      have e2 := path_exists_at_ok hfs hn hr2
      rw [ev2] at e2
      dsimp only at h
      cases b1 <;> cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · cases Result.ok_injective h
        exact ⟨e1, e2, rfl⟩
      all_goals exact absurd h (not_ok_of_err (by err_any))

/-- The name `read_files_at`'s accept read. -/
theorem read_files_at_name {l level o} (h : read_files_at inst fsv pers ar l m level = ok (.Ok o)) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [read_files_at] at h
  peel h as s0, -
  peel h as v, -
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    rw [read_part_at] at hr1
    peel hr1 as r2, hr2
    cases r2 with
    | Err e => cases Result.ok_injective hr1
    | Ok q => exact mod_file_name hr2

/-- **`read_files_at`' accept is the twin's `readFilesAt`.** -/
theorem read_files_at_refines {l : Located} {level o}
    (hfs : FsRel inst fsv fs) (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files_at inst fsv pers ar l m level = ok (.Ok o)) :
    ∃ f', Arena.Frontend.Olean.readFilesAt fs (absLocated l) (absName n) (absLevel level) = .ok f' ∧
      ModFilesRel o f' := by
  rw [read_files_at] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean" := abs_olean_lit (by unfold read_files_at.M; decide) hs0 hv
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok ex =>
    have hE := fun a => (read_part_at_ok hfs hn hr1 a).1
    have hfit := (read_part_at_ok hfs hn hr1 (fun _ => .internal "")).2
    rw [ev] at hE
    have hE' : ∀ a, readPartOr fs (ConLeche.Frontend.Olean.modFile (absLocated l).dir (absName n) "olean") a =
        .ok (absPart ex) := hE
    dsimp only at h
    cases level with
    | Exported =>
      cases Result.ok_injective h
      exact ⟨_, readFilesAt_exported hE', mf_rel_exported hfit⟩
    | Server =>
      dsimp only at h
      peel h as b, hb
      have eb := mod_files_is_module_eq (mf_rel_exported hfit) hb
      by_cases hc : b = true
      · rw [ite_eq_left hc] at h
        subst hc
        obtain ⟨s, e1, hs, e2, rfl⟩ := read_files_parts_server hfs hn h
        exact ⟨_, readFilesAt_server hE' eb.symm e1 e2,
          ⟨rfl, rfl, rfl, hfit, by rintro _ ⟨rfl⟩; exact hs, by simp⟩⟩
      · rw [ite_eq_right hc] at h
        obtain ⟨c1, c2, rfl⟩ := classic_arm hfs hn h
        have hc' : b = false := by simpa using hc
        subst hc'
        exact ⟨_, readFilesAt_classic (by simp [absLevel]) hE' eb.symm c1 c2, mf_rel_exported hfit⟩
    | Private =>
      dsimp only at h
      peel h as b, hb
      have eb := mod_files_is_module_eq (mf_rel_exported hfit) hb
      by_cases hc : b = true
      · rw [ite_eq_left hc] at h
        subst hc
        obtain ⟨s, q, e1, hs, e2, hq, rfl⟩ := read_files_parts_private hfs hn h
        exact ⟨_, readFilesAt_private hE' eb.symm e1 e2,
          ⟨rfl, rfl, rfl, hfit, by rintro _ ⟨rfl⟩; exact hs, by rintro _ ⟨rfl⟩; exact hq⟩⟩
      · rw [ite_eq_right hc] at h
        obtain ⟨c1, c2, rfl⟩ := classic_arm hfs hn h
        have hc' : b = false := by simpa using hc
        subst hc'
        exact ⟨_, readFilesAt_classic (by simp [absLevel]) hE' eb.symm c1 c2, mf_rel_exported hfit⟩

/-- The name `read_files`' accept read. -/
theorem read_files_name {sp level o} (h : read_files inst fsv pers ar sp m level = ok (.Ok o)) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [read_files] at h
  peel h as r, -
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok l => exact read_files_at_name h

/-- **`read_files`' accept is the twin's `readFiles`.** -/
theorem read_files_refines {sp : frontend.olean.files.Roots} {level o}
    (hfs : FsRel inst fsv fs) (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files inst fsv pers ar sp m level = ok (.Ok o)) :
    ∃ f', Arena.Frontend.Olean.readFiles fs (absRoots sp) (absName n) (absLevel level) = .ok f' ∧
      ModFilesRel o f' := by
  rw [read_files] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok l =>
    have hF := find_module_ok hfs hn hr
    obtain ⟨f', e1, hrel⟩ := read_files_at_refines hfs hn h
    exact ⟨f', by simp only [Arena.Frontend.Olean.readFiles, Bind.bind, Except.bind, hF, e1], hrel⟩

end files

end reads

end ConRon.Refine2.Frontend.Olean

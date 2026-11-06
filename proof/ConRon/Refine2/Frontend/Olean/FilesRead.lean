/-
# `ConRon.Refine2.Frontend.Olean.FilesRead` — a module's reads, in `olean/files.rs`

**Task #142, Theorem 2.**  What the search of `Files.lean` answers, read: the header's chunks,
the imports, the files a view reads, a view.  Each reaches a file read, so each claims its
accept (`AS`, or `.ok` of the twin for a pure one).

`first_bad_view`, `missing_part` carry no theorem: they only build a failure, and a failure of
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
open Arena.Frontend.Olean (findModule readPart hdrShort readHdrBytes hdrChunkN)

/-- **`hdr_short` is `hdrShort`**, of fewer than `2 ^ 60` bytes. -/
theorem hdr_short_eq {acc : alloc.vec.Vec Std.U8} {b : Bool} (hb : acc.val.length < 2 ^ 60)
    (h : hdr_short acc = ok b) : b = hdrShort (absBytes (alloc.vec.Vec.deref acc)) := by
  rw [hdr_short] at h
  peel h as w, hw
  have ew := hdr_walk_eq (by rw [deref_val]; exact hb) hw
  rw [show frontend.olean.region.DATA_START.val = ConLeche.Frontend.Olean.dataStart from data_start_val] at ew
  rw [hdrShort, ← ew]
  cases w <;> exact (Result.ok_injective h).symm

/-! ## The literals -/

theorem abs_olean_lit {M : Std.Array Std.U32 5#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) = ['o', 'l', 'e', 'a', 'n'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

theorem abs_server_lit {M : Std.Array Std.U32 12#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 's', 'e', 'r', 'v', 'e', 'r'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean.server" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

theorem abs_private_lit {M : Std.Array Std.U32 13#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 'p', 'r', 'i', 'v', 'a', 't', 'e'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean.private" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

/-- Whatever precedes it, a tail that ends in an `Err`. -/
macro "err_any" : tactic => `(tactic| (
  repeat' first
    | exact fun _ h => ⟨_, (Result.ok_injective h).symm⟩
    | (refine ConRon.Refine2.Lockstep.LSP.bind_eq fun _ _ => ?_)))

theorem not_ok_of_err {α : Type} {m : Result (core.result.Result α kernel.core_types.CheckError)} {a}
    (hm : LSP m (fun o => ∃ e, o = .Err e)) : m ≠ ok (.Ok a) := by
  intro h
  obtain ⟨_, he⟩ := hm _ h
  cases he

section reads

variable {F : Type} {inst : OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}

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
      | Err e => cases Result.ok_injective h
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
    {st : arena.monad.AState} {lst : AState} {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {m : arena.handle.NIdx} (hfs : FsRel inst fsv fs) :
    AS pers (EqA absImports) st lst (module_imports inst fsv pk pers st.store sp m)
      (Arena.Frontend.Olean.moduleImports fs (absPins pk) (absSearchPath sp) (absNIdx m)) := by
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
open Arena.Frontend.Olean (readFiles)
variable {sp : List System.FilePath} {m : ConLeche.Name} {loc : ConLeche.Frontend.Olean.Located} {ex : Part}

theorem readFiles_exported (hF : findModule fs sp m = .ok loc)
    (hE : readPart fs (modFile loc.dir m "olean") = .ok ex) :
    readFiles fs sp m .exported = .ok { exported := ex } := by
  simp only [readFiles, Bind.bind, Except.bind, hF, hE]
  rfl

theorem readFiles_classic {level : OLeanLevel} (hl : level ≠ .exported) (hF : findModule fs sp m = .ok loc)
    (hE : readPart fs (modFile loc.dir m "olean") = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = false) (hs : loc.hasServer = false)
    (hp : loc.hasPrivate = false) :
    readFiles fs sp m level = .ok { exported := ex } := by
  have hl' : (level == .exported) = false := by cases level <;> first | rfl | exact absurd rfl hl
  simp only [readFiles, Bind.bind, Except.bind, hF, hE, hl', hM, hs, hp]
  rfl

theorem readFiles_server {s : Part} (hF : findModule fs sp m = .ok loc)
    (hE : readPart fs (modFile loc.dir m "olean") = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = true) (hs : loc.hasServer = true)
    (hp : loc.hasPrivate = true) (hS : readPart fs (modFile loc.dir m "olean.server") = .ok s) :
    readFiles fs sp m .server = .ok { exported := ex, server := some s } := by
  simp only [readFiles, Bind.bind, Except.bind, hF, hE, hM, hs, hp, hS]
  rfl

theorem readFiles_private {s p : Part} (hF : findModule fs sp m = .ok loc)
    (hE : readPart fs (modFile loc.dir m "olean") = .ok ex)
    (hM : ModFiles.isModule { exported := ex } = true) (hs : loc.hasServer = true)
    (hp : loc.hasPrivate = true) (hS : readPart fs (modFile loc.dir m "olean.server") = .ok s)
    (hP : readPart fs (modFile loc.dir m "olean.private") = .ok p) :
    readFiles fs sp m .private = .ok { exported := ex, server := some s, «private» := some p } := by
  simp only [readFiles, Bind.bind, Except.bind, hF, hE, hM, hs, hp, hS, hP]
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
    ∃ s, readPart fs (fileQ l.dir n "olean.server") = .ok (absPart s) ∧ PartFits s ∧
      o = { f with server := some s, private_part := none } := by
  rw [read_files_parts] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean.server" := abs_server_lit (by unfold read_files_parts.M; decide) hs0 hv
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrel := pathRel_of hn hr
    rw [ev] at hrel
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok s =>
      obtain ⟨e1, hf⟩ := read_part_ok hfs hrel hr1
      cases Result.ok_injective h
      exact ⟨s, e1, hf, rfl⟩

theorem read_files_parts_private {l : Located} {f o} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files_parts inst fsv pers ar m l f .Private = ok (.Ok o)) :
    ∃ s p, readPart fs (fileQ l.dir n "olean.server") = .ok (absPart s) ∧ PartFits s ∧
      readPart fs (fileQ l.dir n "olean.private") = .ok (absPart p) ∧ PartFits p ∧
      o = { f with server := some s, private_part := some p } := by
  rw [read_files_parts] at h
  peel h as s0, hs0
  peel h as v, hv
  have ev : absString v = "olean.server" := abs_server_lit (by unfold read_files_parts.M; decide) hs0 hv
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrel := pathRel_of hn hr
    rw [ev] at hrel
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok s =>
      obtain ⟨e1, hf⟩ := read_part_ok hfs hrel hr1
      dsimp only at h
      peel h as s1, hs1
      peel h as v1, hv1
      have ev1 : absString v1 = "olean.private" :=
        abs_private_lit (by unfold read_files_parts.M_1; decide) hs1 hv1
      peel h as r2, hr2
      cases r2 with
      | Err e => cases Result.ok_injective h
      | Ok p2 =>
        have hrel2 := pathRel_of hn hr2
        rw [ev1] at hrel2
        dsimp only at h
        peel h as r3, hr3
        cases r3 with
        | Err e => cases Result.ok_injective h
        | Ok q =>
          obtain ⟨e2, hf2⟩ := read_part_ok hfs hrel2 hr3
          cases Result.ok_injective h
          exact ⟨s, q, e1, hf, e2, hf2, rfl⟩

/-- The tail of `read_files` above the exported part, at a level past it. -/
theorem rest_arm {α : Type} {b hs hp : Bool} {parts e1 e2 e3 e4 : Result (core.result.Result α kernel.core_types.CheckError)}
    {F0 o : α}
    (h1 : LSP e1 (fun o => ∃ e, o = .Err e)) (h2 : LSP e2 (fun o => ∃ e, o = .Err e))
    (h3 : LSP e3 (fun o => ∃ e, o = .Err e)) (h4 : LSP e4 (fun o => ∃ e, o = .Err e))
    (h : (if b then (if hs then (if hp then parts else e1) else e2)
        else (if hs then e3 else (if hp then e4 else ok (.Ok F0)))) = ok (.Ok o)) :
    (b = false ∧ hs = false ∧ hp = false ∧ o = F0) ∨ (b = true ∧ hs = true ∧ hp = true ∧ parts = ok (.Ok o)) := by
  cases b <;> cases hs <;> cases hp <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · refine .inl ⟨rfl, rfl, rfl, ?_⟩
    cases Result.ok_injective h; rfl
  · exact absurd h (not_ok_of_err h4)
  · exact absurd h (not_ok_of_err h3)
  · exact absurd h (not_ok_of_err h3)
  · exact absurd h (not_ok_of_err h2)
  · exact absurd h (not_ok_of_err h2)
  · exact absurd h (not_ok_of_err h1)
  · exact .inr ⟨rfl, rfl, rfl, h⟩

theorem mf_rel_exported {p : frontend.olean.region.Part} (hf : PartFits p) :
    ModFilesRel { exported := p, server := none, private_part := none } { exported := absPart p } :=
  ⟨rfl, rfl, rfl, hf, by simp, by simp⟩

/-- The name `read_files`' accept read. -/
theorem read_files_name {sp level o} (h : read_files inst fsv pers ar sp m level = ok (.Ok o)) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [read_files] at h
  peel h as r, -
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok l =>
    dsimp only at h
    peel h as mt, -
    peel h as s0, -
    peel h as v, -
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok p => exact mod_file_name hr1

/-- **`read_files`' accept is the twin's `readFiles`.** -/
theorem read_files_refines {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {level o}
    (hfs : FsRel inst fsv fs) (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_files inst fsv pers ar sp m level = ok (.Ok o)) :
    ∃ f', Arena.Frontend.Olean.readFiles fs (absSearchPath sp) (absName n) (absLevel level) = .ok f' ∧
      ModFilesRel o f' := by
  rw [read_files] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok l =>
    have hF := find_module_ok hfs hn hr
    dsimp only at h
    peel h as mt, -
    peel h as s0, hs0
    peel h as v, hv
    have ev : absString v = "olean" := abs_olean_lit (by unfold read_files.M; decide) hs0 hv
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok p =>
      have hrel := pathRel_of hn hr1
      rw [ev] at hrel
      dsimp only at h
      peel h as r2, hr2
      cases r2 with
      | Err e => cases Result.ok_injective h
      | Ok ex =>
        obtain ⟨hE, hfit⟩ := read_part_ok hfs hrel hr2
        have hE' : readPart fs (ConLeche.Frontend.Olean.modFile (absLocated l).dir (absName n) "olean") = .ok (absPart ex) := hE
        dsimp only at h
        cases level with
        | Exported =>
          cases Result.ok_injective h
          exact ⟨_, readFiles_exported hF hE', mf_rel_exported hfit⟩
        | Server =>
          dsimp only at h
          peel h as b, hb
          have eb := mod_files_is_module_eq (mf_rel_exported hfit) hb
          rcases rest_arm (by err_any) (by err_any) (by err_any) (by err_any) h with
            ⟨rfl, c1, c2, rfl⟩ | ⟨rfl, c1, c2, hp⟩
          · exact ⟨_, readFiles_classic (by simp [absLevel]) hF hE' eb.symm c1 c2, mf_rel_exported hfit⟩
          · obtain ⟨s, e1, hs, rfl⟩ := read_files_parts_server hfs hn hp
            exact ⟨_, readFiles_server hF hE' eb.symm c1 c2 e1,
              ⟨rfl, rfl, rfl, hfit, by rintro _ ⟨rfl⟩; exact hs, by simp⟩⟩
        | Private =>
          dsimp only at h
          peel h as b, hb
          have eb := mod_files_is_module_eq (mf_rel_exported hfit) hb
          rcases rest_arm (by err_any) (by err_any) (by err_any) (by err_any) h with
            ⟨rfl, c1, c2, rfl⟩ | ⟨rfl, c1, c2, hp⟩
          · exact ⟨_, readFiles_classic (by simp [absLevel]) hF hE' eb.symm c1 c2, mf_rel_exported hfit⟩
          · obtain ⟨s, q, e1, hs, e2, hq, rfl⟩ := read_files_parts_private hfs hn hp
            exact ⟨_, readFiles_private hF hE' eb.symm c1 c2 e1 e2,
              ⟨rfl, rfl, rfl, hfit, by rintro _ ⟨rfl⟩; exact hs, by rintro _ ⟨rfl⟩; exact hq⟩⟩

end files

end reads

end ConRon.Refine2.Frontend.Olean

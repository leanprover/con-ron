/-
# `ConRon.Bridge.Frontend.Olean.Files` — the reads on one snapshot

The twin reads through a record of five functions.  **`modelFs F` is the record of a snapshot
`F`**: upstream's `ModelIO` operations on `F`, with a message where the snapshot has no answer;
its positional `readRange p off len` is the slice a handle of `p` at position `off` reads
(`ModelIO.read`).  Over it each read of the twin that answers is what upstream's read gives on
`F` (`ModelIO.Gives`: one answer from any open handles), so it can give it (`ModelIO.CanGive`),
which is what `readFiles_ok`, `closureOrder_ok` and `readView_of_viewOf` speak of.

The binary's record is related to `modelFs F` by the theorems' file premise, `ConRon/Capstone.lean`'s
`SnapshotOf`.
-/
module

public import ConRon.Arena.Frontend.Olean.Closure
public import ConRon.Bridge.Frontend.Olean.Parse
public import ConLeche.Verify.Frontend.Olean.Files
public import ConRon.Bridge.Frontend.Lines

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins OleanFs partOfBytes toArenaError)
open ConLeche.Frontend.Olean (ImportF ImportRec Part Located modFile partExts OLeanLevel ModFiles
  hdrChunk hdrStep hdrFin hdrWalk dataStart SearchPath undecodable)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:357-364 instCheckerIOModelIO — **the twin's
record of a snapshot**: `ModelIO`'s operations, a message where they have no value.  The twin
reads a range by position: `readRange p off len` is what a handle of `p` at `off` reads
(`ModelIO.read`), the slice of the file's bytes from `off`, `len` long but at the end. -/
@[expose] def modelFs (F : FS) : OleanFs where
  pathExists p := .ok (F.real p).isSome
  realPath p := match F.real p with
    | some q => .ok q
    | none => .error "no such file"
  readBinFile p := match F.file p with
    | some b => .ok b
    | none => .error "no such file"
  readRange p off len := match F.file p with
    | some b => .ok (b.extract off (min (off + len) b.size))
    | none => .error "no such file"
  fileSize p := match F.file p with
    | some b => .ok b.size
    | none => .error "no such file"

theorem modelFs_readBinFile {F : FS} {p : System.FilePath} {b : ByteArray}
    (h : (modelFs F).readBinFile p = .ok b) : F.file p = some b := by
  simp only [modelFs] at h
  cases hr : F.file p with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    cases h
    rfl

theorem pathExists_gives (F : FS) (p : System.FilePath) :
    ModelIO.Gives (CheckerIO.pathExists p : ModelIO Bool) F (F.real p).isSome :=
  fun hs => ⟨hs, rfl⟩

theorem realPath_gives {F : FS} {p q : System.FilePath} (h : F.real p = some q) :
    ModelIO.Gives (CheckerIO.realPath p : ModelIO System.FilePath) F q :=
  fun hs => ⟨hs, by show ModelIO.ret (F.real p) hs = _; rw [h]⟩

theorem modelFs_fileSize {F : FS} {p : System.FilePath} {n : Nat}
    (h : (modelFs F).fileSize p = .ok n) : ∃ b, F.file p = some b ∧ n = b.size := by
  simp only [modelFs] at h
  cases hr : F.file p with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    cases h
    exact ⟨r, rfl, rfl⟩

/-! ## Except -/

theorem except_ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Locating a module -/

theorem locateIn_sim {F : FS} {m : ConLeche.Name} {d : System.FilePath}
    {x : System.FilePath × List (Option String)}
    (h : Arena.Frontend.Olean.locateIn (modelFs F) m d = .ok x) :
    ModelIO.Gives (ConLeche.Frontend.Olean.locateIn m d : ModelIO _) F x := by
  unfold Arena.Frontend.Olean.locateIn at h
  unfold ConLeche.Frontend.Olean.locateIn
  obtain ⟨fsv, h1, h2⟩ := except_ok_of_bind h
  cases h2
  have key : ∀ (l : List String) {ys : List (Option String)},
      (l.mapM fun e => do
        let p := modFile d m e
        if ← (modelFs F).pathExists p then
          return some (← (modelFs F).realPath p).toString
        else return none) = (.ok ys : Except String _) →
      ModelIO.Gives (l.mapM fun e => do
        let p := modFile d m e
        if ← (CheckerIO.pathExists p : ModelIO Bool) then
          return some (← (CheckerIO.realPath p : ModelIO _)).toString
        else return none) F ys := by
    intro l
    induction l with
    | nil =>
      intro ys hy
      simp only [List.mapM_nil] at hy ⊢
      cases hy
      exact ModelIO.gives_pure _ _
    | cons e es ih =>
      intro ys hy
      simp only [List.mapM_cons] at hy ⊢
      obtain ⟨y, hy1, hy2⟩ := except_ok_of_bind hy
      obtain ⟨ys', hy3, hy4⟩ := except_ok_of_bind hy2
      cases hy4
      refine ModelIO.Gives.bind ?_ ((ih hy3).bind (ModelIO.gives_pure _ _))
      obtain ⟨b, hb1, hb2⟩ := except_ok_of_bind hy1
      refine (pathExists_gives F _).bind ?_
      cases hr : F.real (modFile d m e) with
      | none =>
        simp only [modelFs, hr, Option.isSome_none, Except.ok.injEq] at hb1
        subst hb1
        simp only [Bool.false_eq_true, ↓reduceIte] at hb2
        cases hb2
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        exact ModelIO.gives_pure _ _
      | some q =>
        simp only [modelFs, hr, Option.isSome_some, Except.ok.injEq] at hb1
        subst hb1
        simp only [↓reduceIte, modelFs, hr] at hb2
        cases hb2
        simp only [Option.isSome_some, ↓reduceIte]
        exact (realPath_gives hr).bind (ModelIO.gives_pure _ _)
  exact (key _ h1).bind (ModelIO.gives_pure _ _)

theorem locateHits_sim {F : FS} {sp : SearchPath} {m : ConLeche.Name}
    {x : Array (System.FilePath × List (Option String))}
    (h : Arena.Frontend.Olean.locateHits (modelFs F) sp m = .ok x) :
    ModelIO.Gives (ConLeche.Frontend.Olean.locateHits sp m : ModelIO _) F x := by
  unfold Arena.Frontend.Olean.locateHits at h
  unfold ConLeche.Frontend.Olean.locateHits
  obtain ⟨hs, h1, h2⟩ := except_ok_of_bind h
  cases h2
  have key : ∀ (l : List System.FilePath) {ys : List (System.FilePath × List (Option String))},
      (l.mapM (Arena.Frontend.Olean.locateIn (modelFs F) m)) = .ok ys →
      ModelIO.Gives (l.mapM (ConLeche.Frontend.Olean.locateIn m) : ModelIO _) F ys := by
    intro l
    induction l with
    | nil =>
      intro ys hy
      simp only [List.mapM_nil] at hy ⊢
      cases hy
      exact ModelIO.gives_pure _ _
    | cons e es ih =>
      intro ys hy
      simp only [List.mapM_cons] at hy ⊢
      obtain ⟨y, hy1, hy2⟩ := except_ok_of_bind hy
      obtain ⟨ys', hy3, hy4⟩ := except_ok_of_bind hy2
      cases hy4
      exact (locateIn_sim hy1).bind ((ih hy3).bind (ModelIO.gives_pure _ _))
  exact (key _ h1).bind (ModelIO.gives_pure _ _)

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:73 findModule_ok -/
theorem findModule_sim {F : FS} {sp : SearchPath} {m : ConLeche.Name} {l : Located}
    (h : Arena.Frontend.Olean.findModule (modelFs F) sp m = .ok l) :
    ModelIO.Gives (ConLeche.Frontend.Olean.findModule sp m : ModelIO _) F (.ok l) := by
  unfold Arena.Frontend.Olean.findModule at h
  unfold ConLeche.Frontend.Olean.findModule
  split at h
  · rename_i hits hh
    split at h
    · rename_i l' hl
      cases h
      refine (locateHits_sim hh).map.tryCatch.bind ?_
      simp only [hl]
      exact ModelIO.gives_pure _ _
    · cases h
  · cases h

/-! ## One file -/

/-- con-leche: ConLeche/Frontend/Olean/Region.lean:103-119 Part.ofBytes — the path is the
messages'. -/
theorem ofBytes_label {p p' : String} {b : ByteArray} {x : Part} (h : Part.ofBytes p b = .ok x) :
    Part.ofBytes p' b = .ok x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ConLeche.Frontend.Olean.Part.ofBytes_checks h
  unfold Part.ofBytes at h ⊢
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h ⊢
  simp only [ge_iff_le, h1, h2, h3, h4, h5, h6, ↓reduceIte] at h ⊢
  exact h

/-- con-leche: none — the twin's validation, the port's size limit aside. -/
theorem partOfBytes_ok {path p' : String} {b : ByteArray} {x : Part} (h : partOfBytes path b = .ok x) :
    Part.ofBytes p' b = .ok x := by
  unfold partOfBytes at h
  split at h
  · cases h
  · split at h
    · rename_i q hq
      cases h
      exact ofBytes_label hq
    · cases h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:114 readPart_det -/
theorem readPart_sim {F : FS} {p : System.FilePath} {x : Part}
    (h : Arena.Frontend.Olean.readPart (modelFs F) p = .ok x) :
    ModelIO.Gives (ConLeche.Frontend.Olean.readPart p : ModelIO _) F (.ok x) := by
  unfold Arena.Frontend.Olean.readPart at h
  split at h
  · cases h
  · rename_i b hb
    have hd := ConLeche.Frontend.Olean.readPart_det (modelFs_readBinFile hb)
    rwa [partOfBytes_ok h] at hd

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:136 foldList_hdr — the twin's reads at
offsets `off`, `off + 4096`, … are the handle's reads from `off` (`readsFrom`). -/
theorem readHdrBytes_fold {F : FS} {p : System.FilePath} {b : ByteArray}
    (hb : F.file p = some b) {path : String} {acc' : ByteArray} {x : Array ImportRec}
    {ex : Part} (hp : Part.ofBytes path acc' = .ok ex)
    (hi : ConLeche.Frontend.Olean.importsPre acc' = some x) :
    ∀ (n off : Nat), b.size - off ≤ n → ∀ {acc : ByteArray}, off ≤ b.size →
      acc = b.extract 0 off →
      Arena.Frontend.Olean.readHdrBytes (modelFs F) p b.size off acc = .ok acc' →
      foldList (hdrStep path) (hdrFin path) acc (readsFrom hdrChunk.toNat b off) = .ok (some x) := by
  intro n
  induction n with
  | zero =>
    intro off hn acc ho hacc h
    have hoff : ¬ off < b.size := by omega
    rw [Arena.Frontend.Olean.readHdrBytes] at h
    simp only [hoff, dite_false, Except.ok.injEq] at h
    subst h
    rw [readsFrom.eq_1]
    simp only [hoff, and_false, dite_false, foldList, hdrFin, hp, Except.map, hi]
  | succ n ih =>
    intro off hn acc ho hacc h
    rw [Arena.Frontend.Olean.readHdrBytes] at h
    by_cases hoff : off < b.size
    · simp only [hoff, dite_true] at h
      have hrr : (modelFs F).readRange p off Arena.Frontend.Olean.hdrChunkN
          = .ok (b.extract off (min (off + Arena.Frontend.Olean.hdrChunkN) b.size)) := by
        simp only [modelFs, hb]
      rw [hrr] at h
      simp only at h
      have hc4 : hdrChunk.toNat = 4096 := ConLeche.Frontend.Olean.hdrChunk_toNat
      have hN : Arena.Frontend.Olean.hdrChunkN = 4096 := rfl
      have hrd : readsFrom 4096 b off =
          b.extract off (min (off + 4096) b.size) :: readsFrom 4096 b (min (off + 4096) b.size) := by
        rw [readsFrom.eq_1]
        rw [dite_eq_left ⟨by decide, hoff⟩]
      rw [hc4, hrd]
      simp only [foldList]
      have happ := ConLeche.Frontend.Olean.extract_step (b := b) (off := off) (csz := 4096) ho (by decide)
      rw [← hacc] at happ
      rw [hN] at h
      rw [happ] at h
      have hstep : hdrStep path acc (b.extract off (min (off + 4096) b.size)) =
          (match hdrWalk (b.extract 0 (min (off + 4096) b.size)) dataStart with
           | .short => .ok (b.extract 0 (min (off + 4096) b.size))
           | _ => .error ((Part.ofBytes path (b.extract 0 (min (off + 4096) b.size))).map
               fun _ => ConLeche.Frontend.Olean.importsPre (b.extract 0 (min (off + 4096) b.size)))) := by
        simp only [hdrStep, happ]
        cases hdrWalk (b.extract 0 (min (off + 4096) b.size)) dataStart <;> rfl
      rw [hstep]
      unfold Arena.Frontend.Olean.hdrShort at h
      cases hw : hdrWalk (b.extract 0 (min (off + 4096) b.size)) dataStart with
      | short =>
        simp only [hw, ↓reduceIte] at h
        simp only
        have hih := ih _ (by omega) (by omega) rfl h
        rwa [hc4] at hih
      | found c e =>
        simp only [hw, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
        subst h
        simp only [hp, Except.map, hi]
      | bad =>
        simp only [hw, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
        subst h
        simp only [hp, Except.map, hi]
    · simp only [hoff, dite_false, Except.ok.injEq] at h
      subst h
      rw [readsFrom.eq_1]
      simp only [hoff, and_false, dite_false, foldList, hdrFin, hp, Except.map, hi]

/-! ## The imports -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:252 readImportsAt_det — **the imports
off the start of a file**, read on the snapshot. -/
theorem readImportsAt_run {pk : OleanPins} {F : FS} {loc : Located} {m : ConLeche.Name}
    {xs : Array (ImportF NIdx)} {s s' : AState} (hctx : Ctx pk s)
    (h : Arena.Frontend.Olean.readImportsAt (modelFs F) pk loc m s = .ok (xs, s')) :
    ParseStep s s' ∧ ∃ zs, ModelIO.Gives (ConLeche.Frontend.Olean.readImportsAt loc m : ModelIO _) F (.ok zs) ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  generalize hF : Arena.Frontend.Olean.readImportsAt (modelFs F) pk loc m = fn at h
  unfold Arena.Frontend.Olean.readImportsAt at hF
  simp only [] at hF
  split at hF
  · subst hF
    cases h
  · rename_i size hsize
    obtain ⟨b, hb, rfl⟩ := modelFs_fileSize hsize
    split at hF
    · subst hF
      cases h
    · rename_i acc hacc
      subst hF
      unfold Arena.Frontend.Olean.hdrFin at h
      cases hpart : partOfBytes (modFile loc.dir m "olean").toString acc with
      | error e =>
        simp only [hpart] at h
        cases h
      | ok part =>
        simp only [hpart] at h
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        cases o with
        | none => cases h2
        | some imps =>
          obtain ⟨hv, hs⟩ := AM.pure_ok h2
          cases hv
          subst hs
          obtain ⟨hst, zs, hz, hd⟩ := importsPre_run hctx h1
          refine ⟨hst, zs, ?_, hd⟩
          have hp : Part.ofBytes (modFile loc.dir m "olean").toString acc = .ok part :=
            partOfBytes_ok hpart
          have hf := readHdrBytes_fold hb hp hz b.size 0 (by omega) (by omega)
            (by simp) hacc
          simp only [ConLeche.Frontend.Olean.readImportsAt]
          refine (ConLeche.foldChunks_det _ _ _ _ hb).bind ?_
          rw [hf]
          exact ModelIO.gives_pure _ _

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:199-205 moduleImports -/
theorem moduleImports_run {pk : OleanPins} {F : FS} {sp : SearchPath} {m : NIdx}
    {mn : ConLeche.Name} {xs : Array (ImportF NIdx)} {s s' : AState}
    (hm : denoteN s.store.ns m = some mn) (hctx : Ctx pk s)
    (h : Arena.Frontend.Olean.moduleImports (modelFs F) pk sp m s = .ok (xs, s')) :
    ParseStep s s' ∧ ∃ zs, ModelIO.Gives (ConLeche.Frontend.Olean.moduleImports sp mn : ModelIO _) F (.ok zs) ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  unfold Arena.Frontend.Olean.moduleImports at h
  obtain ⟨mn', s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hs1, hd1⟩ := readName_run h1
  subst hs1
  have hmn : mn' = mn := Option.some.inj (hd1.symm.trans hm)
  subst hmn
  cases hfm : Arena.Frontend.Olean.findModule (modelFs F) sp mn' with
  | error e =>
    simp only [hfm] at h2
    cases h2
  | ok loc =>
    simp only [hfm] at h2
    obtain ⟨hst, zs, hz, hd⟩ := readImportsAt_run hctx h2
    refine ⟨hst, zs, ?_, hd⟩
    simp only [ConLeche.Frontend.Olean.moduleImports]
    exact (findModule_sim hfm).bind hz

/-! ## The files of a view -/

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:207-236 readFiles -/
theorem readFiles_sim {F : FS} {sp : SearchPath} {m : ConLeche.Name} {level : OLeanLevel}
    {f : ModFiles} (h : Arena.Frontend.Olean.readFiles (modelFs F) sp m level = .ok f) :
    ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp m level : ModelIO _) F (.ok f) := by
  unfold Arena.Frontend.Olean.readFiles at h
  obtain ⟨loc, h1, h⟩ := except_ok_of_bind h
  obtain ⟨ex, h2, h⟩ := except_ok_of_bind h
  unfold ConLeche.Frontend.Olean.readFiles
  refine (findModule_sim h1).bind ?_
  refine (readPart_sim h2).bind ?_
  by_cases he : (level == OLeanLevel.exported) = true
  · simp only [he, ↓reduceIte] at h ⊢
    cases h
    exact ModelIO.gives_pure _ _
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hm : ModFiles.isModule { exported := ex } with
    | false =>
      simp only [hm, Bool.not_false, ↓reduceIte] at h ⊢
      by_cases hs1 : (loc.hasServer || loc.hasPrivate) = true
      · simp only [hs1, ↓reduceIte] at h
        cases h
      · simp only [hs1, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases h
        exact ModelIO.gives_pure _ _
    | true =>
      simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hs : loc.hasServer with
      | false =>
        simp only [hs, Bool.not_false, ↓reduceIte] at h
        cases h
      | true =>
        simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hq : loc.hasPrivate with
        | false =>
          simp only [hq, Bool.not_false, ↓reduceIte] at h
          cases h
        | true =>
          simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h ⊢
          obtain ⟨sv, h3, h⟩ := except_ok_of_bind h
          refine (readPart_sim h3).bind ?_
          by_cases hl : (level == OLeanLevel.server) = true
          · simp only [hl, ↓reduceIte] at h ⊢
            cases h
            exact ModelIO.gives_pure _ _
          · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
            obtain ⟨pv, h4, h⟩ := except_ok_of_bind h
            cases h
            exact (readPart_sim h4).bind (ModelIO.gives_pure _ _)

end ConRon.Bridge.Frontend.Olean

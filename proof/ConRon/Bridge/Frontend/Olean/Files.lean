/-
# `ConRon.Bridge.Frontend.Olean.Files` — the reads on one snapshot

The twin reads through a record of five functions.  **`modelFs F` is the record of a snapshot
`F`**: upstream's `ModelIO` operations on `F`, with a message where the snapshot has no answer;
its positional `readRange p off len` is the slice a handle of `p` at position `off` reads
(`ModelIO.read`).  Over it each read of the twin that answers is what upstream's read gives on
`F` (`ModelIO.Gives`: one answer from any open handles), so it can give it (`ModelIO.CanGive`),
which is what `readFiles_ok`, `closureOrder_ok` and `readView_of_viewOf` speak of.

The binary's record is related to `modelFs F` by the theorems' file premise, `ConRon/MainTheorem/Stages.lean`'s
`SnapshotOf`.
-/
module

public import ConRon.Arena.Frontend.Olean.Closure
public import ConRon.Bridge.Frontend.Olean.Parse
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.Roots
public import ConRon.Bridge.Frontend.Lines

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins OleanFs partOfBytes toArenaError)
open ConLeche.Frontend.Olean (ImportF ImportRec Part Located RootAt Roots modDir modFile OLeanLevel
  ModFiles hdrChunk hdrStep hdrFin hdrWalk dataStart SearchPath undecodable)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:357-364 instCheckerIOModelIO — **the twin's
record of a snapshot**: `ModelIO`'s operations, a message where they have no value.  The twin
reads a range by position: `readRange p off len` is what a handle of `p` at `off` reads
(`ModelIO.read`), the slice of the file's bytes from `off`, `len` long but at the end. -/
@[expose] def modelFs (F : FS) : OleanFs where
  pathExists p := .ok (F.real p).isSome
  isDir p := .ok (F.dir p)
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

theorem isDir_gives (F : FS) (p : System.FilePath) :
    ModelIO.Gives (CheckerIO.isDir p : ModelIO Bool) F (F.dir p) :=
  fun hs => ⟨hs, rfl⟩

/-- A list's `mapM`, an `Except String` step that answers as a `ModelIO` one gives. -/
theorem mapM_sim {α β : Type} {F : FS} {f : α → Except String β} {g : α → ModelIO β}
    (hfg : ∀ a b, f a = .ok b → ModelIO.Gives (g a) F b) :
    ∀ (l : List α) {ys : List β}, l.mapM f = .ok ys → ModelIO.Gives (l.mapM g) F ys
  | [], ys, h => by
    simp only [List.mapM_nil] at h ⊢
    cases h
    exact ModelIO.gives_pure _ _
  | a :: l, ys, h => by
    simp only [List.mapM_cons] at h ⊢
    obtain ⟨y, hy1, hy2⟩ := except_ok_of_bind h
    obtain ⟨ys', hy3, hy4⟩ := except_ok_of_bind hy2
    cases hy4
    exact (hfg a y hy1).bind ((mapM_sim hfg l hy3).bind (ModelIO.gives_pure _ _))

theorem holdsRoot_sim {F : FS} {r : ConLeche.Name} {d : System.FilePath} {b : Bool}
    (h : Arena.Frontend.Olean.holdsRoot (modelFs F) r d = .ok b) :
    ModelIO.Gives (ConLeche.Frontend.Olean.holdsRoot r d : ModelIO Bool) F b := by
  unfold Arena.Frontend.Olean.holdsRoot at h
  unfold ConLeche.Frontend.Olean.holdsRoot
  refine (isDir_gives F _).bind ?_
  cases hd : F.dir (modDir d r) with
  | true =>
    simp only [modelFs, hd, ↓reduceIte] at h ⊢
    cases h
    exact ModelIO.gives_pure _ _
  | false =>
    simp only [modelFs, hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases h
    exact pathExists_gives F _

theorem rootHits_sim {F : FS} {sp : SearchPath} {r : ConLeche.Name} {a : RootAt}
    (h : Arena.Frontend.Olean.rootHits (modelFs F) sp r = .ok a) :
    ModelIO.Gives (ConLeche.Frontend.Olean.rootHits sp r : ModelIO RootAt) F a := by
  unfold Arena.Frontend.Olean.rootHits at h
  unfold ConLeche.Frontend.Olean.rootHits
  obtain ⟨held, h1, h2⟩ := except_ok_of_bind h
  refine (mapM_sim (g := fun d => do return (d, ← (ConLeche.Frontend.Olean.holdsRoot r d : ModelIO Bool)))
    (fun d x hx => by
      obtain ⟨b, hb1, hb2⟩ := except_ok_of_bind hx
      cases hb2
      exact (holdsRoot_sim hb1).bind (ModelIO.gives_pure _ _)) sp h1).bind ?_
  generalize ((held.filter (·.2)).map (·.1)) = hits at h2 ⊢
  rcases hits with _ | ⟨d, _ | ⟨d2, rest⟩⟩
  · cases h2
    exact ModelIO.gives_pure _ _
  · cases h2
    exact ModelIO.gives_pure _ _
  · dsimp only at h2 ⊢
    obtain ⟨rs, h3, h4⟩ := except_ok_of_bind h2
    refine (mapM_sim (g := fun d => do return (d, ← (CheckerIO.realPath d : ModelIO System.FilePath)))
      (fun d x hx => by
        obtain ⟨q, hq1, hq2⟩ := except_ok_of_bind hx
        cases hq2
        cases hr : F.real d with
        | none => simp [modelFs, hr] at hq1
        | some q' =>
          simp only [modelFs, hr, Except.ok.injEq] at hq1
          subst hq1
          exact (realPath_gives hr).bind (ModelIO.gives_pure _ _)) _ h3).bind ?_
    generalize ConLeche.Frontend.Olean.oneEach rs = o at h4 ⊢
    rcases o with _ | ⟨x, _ | ⟨y, o⟩⟩ <;> (cases h4; exact ModelIO.gives_pure _ _)

/-- **The twin's root lookup on one search path, where no operation failed, is upstream's.** -/
theorem rootAt_sim {F : FS} {sp : SearchPath} {r : ConLeche.Name} {a : RootAt}
    (h : Arena.Frontend.Olean.rootAt (modelFs F) sp r = a) (ha : ∀ e, a ≠ .failed e) :
    ModelIO.Gives (ConLeche.Frontend.Olean.rootAt sp r : ModelIO RootAt) F a := by
  unfold Arena.Frontend.Olean.rootAt at h
  split at h
  · rename_i a' ha'
    subst h
    exact (rootHits_sim ha').tryCatch
  · exact absurd h.symm (ha _)

/-- con-leche: ConLeche/Verify/Frontend/Olean/Roots.lean:226 lookAt_ok — **a directory the
twin's lookup on a path and its fallback finds is upstream's `lookAt`'s**. -/
theorem lookAt_sim {F : FS} {path fallback : SearchPath} {r : ConLeche.Name}
    {d : System.FilePath}
    (h : Arena.Frontend.Olean.lookAt (modelFs F) path fallback r = .dir d) :
    ModelIO.Gives (ConLeche.Frontend.Olean.lookAt path fallback r : ModelIO RootAt) F (.dir d) := by
  unfold Arena.Frontend.Olean.lookAt at h
  unfold ConLeche.Frontend.Olean.lookAt
  generalize ha : Arena.Frontend.Olean.rootAt (modelFs F) path r = a at h
  cases a with
  | dir d' =>
    cases h
    exact (rootAt_sim ha (by simp)).bind (ModelIO.gives_pure _ _)
  | missing =>
    exact (rootAt_sim ha (by simp)).bind (rootAt_sim h (by simp))
  | twice ds => cases h
  | failed e => cases h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Roots.lean:361 findModule_ok — **a module the twin
finds on the snapshot is found by upstream's lookup with no root resolved**. -/
theorem findModule_sim {F : FS} {sp : Roots} {m : ConLeche.Name} {l : Located}
    (h : Arena.Frontend.Olean.findModule (modelFs F) sp m = .ok l) :
    ModelIO.Gives (ConLeche.Frontend.Olean.findModule sp.bare m : ModelIO _) F (.ok l) := by
  unfold Arena.Frontend.Olean.findModule at h
  unfold ConLeche.Frontend.Olean.findModule
  split at h
  · rename_i l' hl
    cases h
    generalize ha : Arena.Frontend.Olean.lookAt (modelFs F) sp.path sp.fallback m.root = a at hl
    have hd : ∃ d, a = .dir d := by
      cases a <;> simp [ConLeche.Frontend.Olean.locatedOf] at hl ⊢
    obtain ⟨d, rfl⟩ := hd
    rw [← hl]
    refine ModelIO.Gives.map ?_
    simp only [ConLeche.Frontend.Olean.Roots.rootOf]
    have e0 : (sp.bare.map[m.root]? : Option RootAt) = none := by
      show (({} : Std.HashMap ConLeche.Name RootAt)[m.root]?) = none
      simp
    rw [e0]
    exact lookAt_sim ha
  · cases h

/-- A lookup with no root resolved is read off every snapshot. -/
theorem roots_ok_of_bare {F : FS} {sp : Roots} (h : sp.bare = sp) : sp.Ok F :=
  h ▸ ConLeche.Frontend.Olean.Roots.ok_bare F sp

/-- **A module the twin finds is found through any lookup read off the snapshot** whose
directories are the twin's (`Roots.Ok`, upstream's `findModule_rev`). -/
theorem findModule_simR {F : FS} {sp : Roots} {R : Roots} (hR : R.Ok F)
    (hb : R.bare = sp.bare) {m : ConLeche.Name} {l : Located}
    (h : Arena.Frontend.Olean.findModule (modelFs F) sp m = .ok l) :
    ModelIO.Gives (ConLeche.Frontend.Olean.findModule R m : ModelIO _) F (.ok l) := by
  obtain ⟨hs', o⟩ := (findModule_sim h).outcome #[]
  rw [← hb] at o
  exact ConLeche.Frontend.Olean.findModule_ok (ConLeche.Frontend.Olean.findModule_rev hR o)

/-- **Resolving a root the twin finds**: the map, with it resolved, read off the snapshot. -/
theorem resolve_sim {F : FS} {sp : Roots} {R : Roots} (hR : R.Ok F)
    (hb : R.bare = sp.bare) {m : ConLeche.Name} {l : Located}
    (h : Arena.Frontend.Olean.findModule (modelFs F) sp m = .ok l) :
    ∃ R1, ModelIO.Gives (R.resolve m : ModelIO Roots) F R1 ∧ R1.Ok F ∧ R1.bare = sp.bare := by
  have hp : R.path = sp.path := show R.bare.path = sp.bare.path from congrArg Roots.path hb
  have hf : R.fallback = sp.fallback :=
    show R.bare.fallback = sp.bare.fallback from congrArg Roots.fallback hb
  unfold Arena.Frontend.Olean.findModule at h
  split at h
  · rename_i l' hl
    generalize ha : Arena.Frontend.Olean.lookAt (modelFs F) sp.path sp.fallback m.root = a at hl
    have hd : ∃ d, a = .dir d := by
      cases a <;> simp [ConLeche.Frontend.Olean.locatedOf] at hl ⊢
    obtain ⟨d, rfl⟩ := hd
    have hg : ModelIO.Gives (ConLeche.Frontend.Olean.lookAt R.path R.fallback m.root :
        ModelIO RootAt) F (.dir d) := by
      rw [hp, hf]
      exact lookAt_sim ha
    have hres : ∃ R1, ModelIO.Gives (R.resolve m : ModelIO Roots) F R1 := by
      unfold ConLeche.Frontend.Olean.Roots.resolve
      by_cases hc : R.map.contains m.root = true
      · exact ⟨R, by simp only [hc, ↓reduceIte]; exact ModelIO.gives_pure _ _⟩
      · refine ⟨{ R with map := R.map.insert m.root (.dir d) }, ?_⟩
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hg.bind (ModelIO.gives_pure _ _)
    obtain ⟨R1, hR1⟩ := hres
    obtain ⟨hs', o⟩ := hR1.outcome #[]
    obtain ⟨hok, hbare⟩ := ConLeche.Frontend.Olean.Roots.resolve_ok hR o
    exact ⟨R1, hR1, hok, hbare.trans hb⟩
  · cases h

/-- The twin's accepting imports read found the module. -/
theorem moduleImports_found {pk : OleanPins} {F : FS} {sp : Roots} {m : NIdx}
    {mn : ConLeche.Name} {xs : Array (ImportF NIdx)} {s s' : AState}
    (hm : denoteN s.store.ns m = some mn)
    (h : Arena.Frontend.Olean.moduleImports (modelFs F) pk sp m s = .ok (xs, s')) :
    ∃ l, Arena.Frontend.Olean.findModule (modelFs F) sp mn = .ok l := by
  unfold Arena.Frontend.Olean.moduleImports at h
  obtain ⟨mn', s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hs1, hd1⟩ := readName_run h1
  have hmn : mn' = mn := Option.some.inj (hd1.symm.trans (hs1 ▸ hm))
  subst hmn
  cases hfm : Arena.Frontend.Olean.findModule (modelFs F) sp mn' with
  | error e =>
    simp only [hfm] at h2
    cases h2
  | ok loc => exact ⟨loc, rfl⟩

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

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:89 readPartOr_det -/
theorem readPartOr_sim {F : FS} {p : System.FilePath} {absent : Unit → ConRon.Arena.CheckError}
    {absentC : IO.Error → ModelIO ConLeche.CheckError} {x : Part}
    (h : Arena.Frontend.Olean.readPartOr (modelFs F) p absent = .ok x) :
    ModelIO.Gives (ConLeche.Frontend.Olean.readPartOr p absentC : ModelIO _) F (.ok x) := by
  unfold Arena.Frontend.Olean.readPartOr at h
  split at h
  · cases h
  · rename_i b hb
    have hd := ConLeche.Frontend.Olean.readPartOr_det (a := absentC) (modelFs_readBinFile hb)
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
          refine (ConLeche.foldChunks_det _ _ _ _ hb).map.tryCatch.bind ?_
          rw [hf]
          exact ModelIO.gives_pure _ _

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:274-280 moduleImports -/
theorem moduleImports_run {pk : OleanPins} {F : FS} {sp : Roots} {R : Roots} (hR : R.Ok F)
    (hb : R.bare = sp.bare) {m : NIdx}
    {mn : ConLeche.Name} {xs : Array (ImportF NIdx)} {s s' : AState}
    (hm : denoteN s.store.ns m = some mn) (hctx : Ctx pk s)
    (h : Arena.Frontend.Olean.moduleImports (modelFs F) pk sp m s = .ok (xs, s')) :
    ParseStep s s' ∧ ∃ zs, ModelIO.Gives (ConLeche.Frontend.Olean.moduleImports R mn : ModelIO _) F (.ok zs) ∧
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
    exact (findModule_simR hR hb hfm).bind hz

/-! ## The files of a view -/

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:297-325 readFilesAt -/
theorem readFilesAt_sim {F : FS} {loc : Located} {m : ConLeche.Name} {level : OLeanLevel}
    {f : ModFiles} (h : Arena.Frontend.Olean.readFilesAt (modelFs F) loc m level = .ok f) :
    ModelIO.Gives (ConLeche.Frontend.Olean.readFilesAt loc m level : ModelIO _) F (.ok f) := by
  unfold Arena.Frontend.Olean.readFilesAt at h
  obtain ⟨ex, h2, h⟩ := except_ok_of_bind h
  unfold ConLeche.Frontend.Olean.readFilesAt
  refine (readPartOr_sim h2).bind ?_
  by_cases he : (level == OLeanLevel.exported) = true
  · simp only [he, ↓reduceIte] at h ⊢
    cases h
    exact ModelIO.gives_pure _ _
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hm : ModFiles.isModule { exported := ex } with
    | false =>
      simp only [hm, Bool.not_false, ↓reduceIte] at h ⊢
      simp only [Arena.Frontend.Olean.pathExistsE, modelFs, bind, Except.bind, pure,
        Except.pure] at h
      refine (pathExists_gives F _).bind ((pathExists_gives F _).bind ?_)
      by_cases hs1 : ((F.real (modFile loc.dir m "olean.server")).isSome ||
          (F.real (modFile loc.dir m "olean.private")).isSome) = true
      · simp only [hs1, ↓reduceIte] at h
        cases h
      · simp only [hs1, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases h
        exact ModelIO.gives_pure _ _
    | true =>
      simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      rename_i sv h3
      refine (readPartOr_sim h3).bind ?_
      by_cases hl : (level == OLeanLevel.server) = true
      · simp only [hl, ↓reduceIte, Arena.Frontend.Olean.pathExistsE, modelFs] at h ⊢
        refine (pathExists_gives F _).bind ?_
        cases hq : (F.real (modFile loc.dir m "olean.private")).isSome with
        | false => simp [hq] at h
        | true =>
          simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases h
          exact ModelIO.gives_pure _ _
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        split at h
        · cases h
        rename_i pv h4
        cases h
        exact (readPartOr_sim h4).bind (ModelIO.gives_pure _ _)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:327-332 readFiles — through any lookup read
off the snapshot whose directories are the twin's. -/
theorem readFiles_sim {F : FS} {sp : Roots} {R : Roots} (hR : R.Ok F)
    (hb : R.bare = sp.bare) {m : ConLeche.Name} {level : OLeanLevel}
    {f : ModFiles} (h : Arena.Frontend.Olean.readFiles (modelFs F) sp m level = .ok f) :
    ModelIO.Gives (ConLeche.Frontend.Olean.readFiles R m level : ModelIO _) F (.ok f) := by
  unfold Arena.Frontend.Olean.readFiles at h
  obtain ⟨loc, h1, h⟩ := except_ok_of_bind h
  unfold ConLeche.Frontend.Olean.readFiles
  exact (findModule_simR hR hb h1).bind (readFilesAt_sim h)

end ConRon.Bridge.Frontend.Olean

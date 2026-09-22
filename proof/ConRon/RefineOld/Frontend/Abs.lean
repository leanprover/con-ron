import ConRon.RefineOld.Frontend.Base
import ConLeche.Frontend.Scan.Fast
import ConLeche.Frontend.ExportC

/-! # The syntax layer's abstraction functions (task #87, phase 3)

Phase 1 (task #85) proved the port's parser *well formed* — statements about
the port alone.  Phase 3 proves it **exact against con-leche**, and this file
is the vocabulary every lemma of that tier is stated in: the bytes, the
positions, the error tags, the scanner's outcome, and the twelve syntax
records of `ConLeche/Frontend/Scan/Types.lean`.

## The four things that have to be decided once

* **Bytes.**  The port's scanner reads a `Slice U8`; con-leche's reads a
  `ByteArray`.  `absBytes` is the map, `absByte` its element, and
  `absBytes_size`/`absBytes_uget` are the two facts every loop needs.

* **Positions.**  The port's positions are `usize` (Aeneas's bounded
  `Std.Usize`, whose `+` *fails* on overflow); con-leche's are `USize` (a
  machine word that wraps).  `absPos i = USize.ofNat i.val` and
  `absPos_toNat` says the round trip is the identity, because a `Std.Usize`
  is below `2 ^ System.Platform.numBits` by construction.  con-leche rules
  wrap-around out by `usizeStep` under `i < b.usize` (`Scan/Fast.lean:66-72`);
  the port's arithmetic *fails* instead of wrapping, so in the accept
  direction there is nothing to reconcile — a port run that returned `ok` did
  not overflow — and `absPos_add_one` is that statement.

* **The one tag con-leche does not have.**  The port reads a stream index into
  a `u64` and reports `ErrTag::IndexOverflow` when it does not fit
  (`scan_types.rs` module note, deviation 1); con-leche reads a `Nat` and has
  no counterpart.  `absErrTag` sends it to `none`, exactly as `absErrKind`
  sends the checker's `CheckError::Native` to `none` (DESIGN.md §3's ruling of
  2026-09-13), and `ScanErrSim` is then vacuous there — the port's own
  failure claims nothing.

* **A `natVal` literal keeps its digits.**  `scan_types::ExprRec::NatVal`
  carries the decimal bytes the scanner read (module note, deviation 2) where
  con-leche's `ExprRec.natVal` carries the `Nat`; `natOfDigits` is the
  conversion, and it is `readNatAt`'s value by `Scan/Fast.lean:499-500`.

## The outcome convention

`ScanRes<T>` is `Result<(T, usize), ScanErr>` in the port (module note,
deviation 3) and a one-constructor inductive in con-leche.  `ScanSim` is the
full-outcome relation between them, in the shape DESIGN.md §3's ruling fixed
for the checker: exact on `.Ok` — the value *and* the position after it — at
the same offset and tag on a mirrored `.Err`, and nothing on `IndexOverflow`.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Bytes -/

/-- One byte of the port's slice as con-leche's `UInt8`. -/
def absByte (c : Std.U8) : UInt8 := UInt8.ofNat c.val

@[simp] theorem absByte_toNat (c : Std.U8) : (absByte c).toNat = c.val := by
  have h : c.val < 256 := by scalar_tac
  simp [absByte, Nat.mod_eq_of_lt h]

/-- The port's byte slice as con-leche's `ByteArray`. -/
def absBytes (b : Slice Std.U8) : ByteArray := ⟨(b.val.map absByte).toArray⟩

@[simp] theorem absBytes_size (b : Slice Std.U8) : (absBytes b).size = b.val.length := by
  simp [absBytes, ByteArray.size]

theorem absBytes_data (b : Slice Std.U8) :
    (absBytes b).data = (b.val.map absByte).toArray := rfl

/-- The byte at an in-range index: the port's slice read, abstracted. -/
theorem absBytes_getElem (b : Slice Std.U8) (i : Nat) (h : i < b.val.length) :
    (absBytes b).data[i]'(by simpa [absBytes] using h) = absByte (b.val[i]'h) := by
  simp [absBytes]

/-- `ByteArray.uget`, which is what con-leche's scanners read a byte with. -/
theorem absBytes_uget (b : Slice Std.U8) (i : USize)
    (h : i.toNat < (absBytes b).size) (h' : i.toNat < b.val.length) :
    (absBytes b).uget i h = absByte (b.val[i.toNat]'h') := by
  simp [ByteArray.uget, absBytes]

/-! ## Positions

The port's `Std.Usize` is a bit-vector of `System.Platform.numBits` bits, and
so is Lean's `USize`, so the map is `USize.ofNat` and it loses nothing. -/

/-- A port position as con-leche's. -/
def absPos (i : Std.Usize) : USize := USize.ofNat i.val

/-- A `Std.Usize` is below `USize.size` by construction: both are
`2 ^ System.Platform.numBits`. -/
theorem usize_val_lt_size (i : Std.Usize) : i.val < USize.size := by
  have h := i.hBounds
  simp [USize.size]
  exact h

@[simp] theorem absPos_toNat (i : Std.Usize) : (absPos i).toNat = i.val := by
  simp [absPos, Nat.mod_eq_of_lt (usize_val_lt_size i)]

theorem absPos_inj {i j : Std.Usize} (h : absPos i = absPos j) : i.val = j.val := by
  have := congrArg USize.toNat h; simpa using this

/-- The port's `usize` addition, inverted: a step the port returned `ok` for
is a step that did not overflow. -/
theorem usize_add_one_inv {i j : Std.Usize} (h : i + 1#usize = ok j) :
    j.val = i.val + 1 := by
  have h2 := UScalar.add_equiv i (1#usize)
  rw [h] at h2
  simp at h2
  scalar_tac

/-- con-leche's `b.usize` is the slice's length: the length of a `Slice` is at
most `Usize.max`, so `Nat.toUSize` loses nothing. -/
theorem absBytes_usize (b : Slice Std.U8) :
    ((absBytes b).usize).toNat = b.val.length := by
  have hlen : b.val.length < USize.size := by
    have h1 : b.val.length ≤ Std.Usize.max := Slice.property b
    have h2 : (Std.Usize.max : Nat) < USize.size := by
      rw [Std.Usize.max_def, Std.Usize.numBits_def]
      simp only [USize.size, Std.UScalarTy.numBits]
      have hp : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
      omega
    omega
  simp [ByteArray.usize, Nat.toUSize, Nat.mod_eq_of_lt hlen]

/-- An in-range position indexes con-leche's array — `usizeInBounds` on the
port's side of the fence. -/
theorem absPos_lt_usize {b : Slice Std.U8} {i : Std.Usize} :
    absPos i < (absBytes b).usize ↔ i.val < b.val.length := by
  rw [USize.lt_iff_toNat_lt, absPos_toNat, absBytes_usize]

/-- **Stepping a position the port accepted is stepping con-leche's.**  The
port's `+` *fails* on overflow, so a run that returned `ok` proves the step is
in range and con-leche's machine word did not wrap. -/
theorem absPos_add_one {i j : Std.Usize} (h : i + 1#usize = ok j) :
    absPos j = absPos i + 1 := by
  have hj : j.val = i.val + 1 := usize_add_one_inv h
  have hb : i.val + 1 < USize.size := by
    have := usize_val_lt_size j; omega
  apply USize.toNat_inj.mp
  have h1 : ((1 : USize)).toNat = 1 := by simp
  simp only [USize.toNat_add, absPos_toNat, h1, hj]
  exact (Nat.mod_eq_of_lt hb).symm

/-! ## `u64` counts and stream indices

Every record field con-leche types `Nat` the port types `u64` (deviation 1 of
`scan_types.rs`'s module note), and the abstraction is the value. -/

/-- A port count/index as con-leche's `Nat`. -/
@[reducible] def absU64 (n : Std.U64) : Nat := n.val

/-- The indices of a list, in order. -/
def absU64s (v : alloc.vec.Vec Std.U64) : List Nat := v.val.map absU64

/-- **A `natVal` literal's decimal digits as its value** (deviation 2).  The
port's scanner keeps the bytes; `readNatAt` (`Scan/Fast.lean:499-500`) is what
con-leche computes from the same run. -/
def natOfDigits (ds : alloc.vec.Vec Std.U8) : Nat :=
  ds.val.foldl (fun a c => a * 10 + (c.val - 48)) 0

/-! ## Errors -/

/-- **The port's scan tag as con-leche's, `none` for the port's own.**
`ErrTag::IndexOverflow` is con-ron's (deviation 1): a stream index or a count
too large for a `u64`, where con-leche reads a `Nat` and cannot fail.  Sending
it to `none` is what makes `ScanErrSim` claim nothing there — the same shape
`absErrKind` gives `CheckError::Native`. -/
def absErrTag : frontend.scan_types.ErrTag → Option ConLeche.Frontend.ErrTag
  | .ExpectedObject => some .expectedObject
  | .ExpectedKey => some .expectedKey
  | .ExpectedColon => some .expectedColon
  | .ExpectedComma => some .expectedComma
  | .ExpectedList => some .expectedList
  | .UnknownKey => some .unknownKey
  | .DuplicateKey => some .duplicateKey
  | .MissingKey => some .missingKey
  | .MixedKeys => some .mixedKeys
  | .ExpectedNat => some .expectedNat
  | .ExpectedString => some .expectedString
  | .ExpectedBool => some .expectedBool
  | .BadEscape => some .badEscape
  | .BadUtf8 => some .badUtf8
  | .BadBinderInfo => some .badBinderInfo
  | .BadHints => some .badHints
  | .BadPw => some .badPw
  | .BadNatVal => some .badNatVal
  | .Trailing => some .trailing
  | .NoProgress => some .noProgress
  | .IndexOverflow => none

/-- A mirrored scan error, with its offset. -/
def absScanErr (e : frontend.scan_types.ScanErr) : Option ConLeche.Frontend.ScanErr :=
  (absErrTag e.what).map fun t => ⟨e.offset.val, t⟩

/-! ## The scanner's outcome

`ScanRes<T> = Result<(T, usize), ScanErr>` (deviation 3) against con-leche's
one-constructor `ScanRes α`.  The full-outcome convention of DESIGN.md §3:
exact on `.Ok`, the **same offset and tag** on a mirrored `.Err`, nothing on
`IndexOverflow`. -/

/-- *"If the port's scan error has a con-leche tag, con-leche fails there, at
the same offset."* -/
def ScanErrSim {α : Type} (e : frontend.scan_types.ScanErr)
    (x : ConLeche.Frontend.ScanRes α) : Prop :=
  ∀ le, absScanErr e = some le → x = .err le

/-- The port's own failure claims nothing. -/
theorem ScanErrSim.of_none {α : Type} {e : frontend.scan_types.ScanErr}
    {x : ConLeche.Frontend.ScanRes α} (h : absErrTag e.what = none) : ScanErrSim e x := by
  intro le hle; rw [absScanErr, h] at hle; simp at hle

theorem ScanErrSim.overflow {α : Type} {e : frontend.scan_types.ScanErr}
    {x : ConLeche.Frontend.ScanRes α}
    (h : e.what = .IndexOverflow) : ScanErrSim e x :=
  ScanErrSim.of_none (by rw [h]; rfl)

/-- A mirrored tag: con-leche fails at the same offset. -/
theorem ScanErrSim.mk {α : Type} {e : frontend.scan_types.ScanErr}
    {x : ConLeche.Frontend.ScanRes α} {t : ConLeche.Frontend.ErrTag}
    (ht : absErrTag e.what = some t) (hx : x = .err ⟨e.offset.val, t⟩) :
    ScanErrSim e x := by
  intro le hle
  rw [absScanErr, ht] at hle
  simp only [Option.map_some, Option.some.injEq] at hle
  rw [hx, ← hle]

/-- **The scanner's full outcome.**  `A` abstracts the value; the position
after the value is claimed exactly. -/
def ScanSim {T α : Type} (A : T → α)
    (o : core.result.Result (T × Std.Usize) frontend.scan_types.ScanErr)
    (x : ConLeche.Frontend.ScanRes α) : Prop :=
  match o with
  | .Ok p => x = .ok (A p.1) (absPos p.2)
  | .Err e => ScanErrSim e x

theorem ScanSim.ok {T α : Type} {A : T → α} {v : T} {p : Std.Usize}
    {x : ConLeche.Frontend.ScanRes α} (h : x = .ok (A v) (absPos p)) :
    ScanSim A (.Ok (v, p)) x := h

theorem ScanSim.err {T α : Type} {A : T → α} {e : frontend.scan_types.ScanErr}
    {x : ConLeche.Frontend.ScanRes α} (h : ScanErrSim e x) :
    ScanSim A (.Err e) x := h

/-! ## The key alphabet -/

/-- `scan_types::Key` against `ConLeche/Frontend/Scan/Types.lean:254-328`. -/
def absKey : frontend.scan_types.Key → ConLeche.Frontend.Key
  | .KUnknown => .kUnknown
  | .KAll => .kAll
  | .KApp => .kApp
  | .KArg => .kArg
  | .KAxiom => .kAxiom
  | .KBinderInfo => .kBinderInfo
  | .KBody => .kBody
  | .KBvar => .kBvar
  | .KCidx => .kCidx
  | .KConst => .kConst
  | .KCtor => .kCtor
  | .KCtors => .kCtors
  | .KDef => .kDef
  | .KFn => .kFn
  | .KForallE => .kForallE
  | .KHints => .kHints
  | .KI => .kI
  | .KIdx => .kIdx
  | .KIe => .kIe
  | .KIl => .kIl
  | .KImax => .kImax
  | .KIn => .kIn
  | .KInduct => .kInduct
  | .KInductive => .kInductive
  | .KIsRec => .kIsRec
  | .KIsReflexive => .kIsReflexive
  | .KIsUnsafe => .kIsUnsafe
  | .KK => .kK
  | .KKind => .kKind
  | .KLam => .kLam
  | .KLetE => .kLetE
  | .KLevelParams => .kLevelParams
  | .KMax => .kMax
  | .KMeta => .kMeta
  | .KName => .kName
  | .KNatVal => .kNatVal
  | .KNfields => .kNfields
  | .KNondep => .kNondep
  | .KNum => .kNum
  | .KNumFields => .kNumFields
  | .KNumIndices => .kNumIndices
  | .KNumMinors => .kNumMinors
  | .KNumMotives => .kNumMotives
  | .KNumNested => .kNumNested
  | .KNumParams => .kNumParams
  | .KOpaque => .kOpaque
  | .KParam => .kParam
  | .KPre => .kPre
  | .KProj => .kProj
  | .KPw => .kPw
  | .KQuot => .kQuot
  | .KRecs => .kRecs
  | .KRegular => .kRegular
  | .KRhs => .kRhs
  | .KRules => .kRules
  | .KSafety => .kSafety
  | .KSort => .kSort
  | .KStr => .kStr
  | .KStrVal => .kStrVal
  | .KStruct => .kStruct
  | .KSucc => .kSucc
  | .KThm => .kThm
  | .KType => .kType
  | .KTypeName => .kTypeName
  | .KTypes => .kTypes
  | .KUs => .kUs
  | .KValue => .kValue

/-! ## The syntax records

One abstraction per record of `ConLeche/Frontend/Scan/Types.lean`, field for
field, with `Vec<u32>` payloads through `absString` and `u64` fields through
`absU64`. -/

/-- `NameRec` (`Types.lean:139-143`). -/
def absNameRec : frontend.scan_types.NameRec → ConLeche.Frontend.NameRec
  | .Str pre s => .str (absU64 pre) (absString s)
  | .Num pre n => .num (absU64 pre) (absU64 n)

/-- `LevelRec` (`Types.lean:145-150`). -/
def absLevelRec : frontend.scan_types.LevelRec → ConLeche.Frontend.LevelRec
  | .Succ u => .succ (absU64 u)
  | .Max u v => .max (absU64 u) (absU64 v)
  | .Imax u v => .imax (absU64 u) (absU64 v)
  | .Param n => .param (absU64 n)

/-- `PwRec` (`Types.lean:152-156`). -/
def absPwRec : frontend.scan_types.PwRec → ConLeche.Frontend.PwRec
  | .Never => .never
  | .IfAllZero ns => .ifAllZero (absU64s ns)

/-- `ExprRec` (`Types.lean:158-172`).  The `NatVal` arm is deviation 2: the
port keeps the literal's decimal digits and `natOfDigits` is their value. -/
def absExprRec : frontend.scan_types.ExprRec → ConLeche.Frontend.ExprRec
  | .Bvar k => .bvar (absU64 k)
  | .Sort u => .sort (absU64 u)
  | .Const n us => .const (absU64 n) (absU64s us)
  | .App f a => .app (absU64 f) (absU64 a)
  | .Lam t b pw => .lam (absU64 t) (absU64 b) (absPwRec pw)
  | .ForallE t b pw => .forallE (absU64 t) (absU64 b) (absPwRec pw)
  | .LetE t v b => .letE (absU64 t) (absU64 v) (absU64 b)
  | .Proj tn i s => .proj (absU64 tn) (absU64 i) (absU64 s)
  | .NatVal ds => .natVal (natOfDigits ds)
  | .StrVal s => .strVal (absString s)

/-- `CVRec` (`Types.lean:174-178`). -/
def absCVRec (cv : frontend.scan_types.CVRec) : ConLeche.Frontend.CVRec :=
  ⟨absU64 cv.name, absU64s cv.level_params, absU64 cv.ty⟩

/-- `HintsRec` (`Types.lean:180-184`). -/
def absHintsRec : frontend.scan_types.HintsRec → ConLeche.Frontend.HintsRec
  | .Abbrev => .abbrev
  | .Opaque => .opaque
  | .Regular n => .regular (absU64 n)

/-- `RuleRec` (`Types.lean:186-190`). -/
def absRuleRec (r : frontend.scan_types.RuleRec) : ConLeche.Frontend.RuleRec :=
  ⟨absU64 r.ctor, absU64 r.nfields, absU64 r.rhs⟩

def absRuleRecs (v : alloc.vec.Vec frontend.scan_types.RuleRec) :
    List ConLeche.Frontend.RuleRec :=
  v.val.map absRuleRec

/-- `IndTypeRec` (`Types.lean:192-201`). -/
def absIndTypeRec (t : frontend.scan_types.IndTypeRec) : ConLeche.Frontend.IndTypeRec :=
  { cv := absCVRec t.cv, ctors := absU64s t.ctors, isRec := t.is_rec,
    isReflexive := t.is_reflexive, isUnsafe := t.is_unsafe,
    numIndices := absU64 t.num_indices, numNested := absU64 t.num_nested,
    numParams := absU64 t.num_params }

def absIndTypeRecs (v : alloc.vec.Vec frontend.scan_types.IndTypeRec) :
    List ConLeche.Frontend.IndTypeRec :=
  v.val.map absIndTypeRec

/-- `IndCtorRec` (`Types.lean:203-216`); `cidx` and `induct` are the dialect's
optional redundant fields. -/
def absIndCtorRec (c : frontend.scan_types.IndCtorRec) : ConLeche.Frontend.IndCtorRec :=
  { cv := absCVRec c.cv, isUnsafe := c.is_unsafe, numFields := absU64 c.num_fields,
    numParams := absU64 c.num_params, cidx := c.cidx.map absU64,
    induct := c.induct.map absU64 }

def absIndCtorRecs (v : alloc.vec.Vec frontend.scan_types.IndCtorRec) :
    List ConLeche.Frontend.IndCtorRec :=
  v.val.map absIndCtorRec

/-- `IndRecRec` (`Types.lean:218-227`). -/
def absIndRecRec (r : frontend.scan_types.IndRecRec) : ConLeche.Frontend.IndRecRec :=
  { cv := absCVRec r.cv, isUnsafe := r.is_unsafe, k := r.k,
    numIndices := absU64 r.num_indices, numMinors := absU64 r.num_minors,
    numMotives := absU64 r.num_motives, numParams := absU64 r.num_params,
    rules := absRuleRecs r.rules }

def absIndRecRecs (v : alloc.vec.Vec frontend.scan_types.IndRecRec) :
    List ConLeche.Frontend.IndRecRec :=
  v.val.map absIndRecRec

/-- `DeclRec` (`Types.lean:229-239`).  `safety` and `kind` keep their
spelling on both sides. -/
def absDeclRec : frontend.scan_types.DeclRec → ConLeche.Frontend.DeclRec
  | .Ax cv u => .ax (absCVRec cv) u
  | .Defn cv v h s => .defn (absCVRec cv) (absU64 v) (absHintsRec h) (absString s)
  | .Thm cv v => .thm (absCVRec cv) (absU64 v)
  | .Opaq cv v u => .opaq (absCVRec cv) (absU64 v) u
  | .Quot cv k => .quot (absCVRec cv) (absString k)
  | .Ind tys cts rs => .ind (absIndTypeRecs tys) (absIndCtorRecs cts) (absIndRecRecs rs)

/-- `LineRec` (`Types.lean:241-250`). -/
def absLineRec : frontend.scan_types.LineRec → ConLeche.Frontend.LineRec
  | .Name i r => .name (absU64 i) (absNameRec r)
  | .Level i r => .level (absU64 i) (absLevelRec r)
  | .Expr i r => .expr (absU64 i) (absExprRec r)
  | .Decl d => .decl (absDeclRec d)
  | .Header => .header
  | .Blank => .blank

/-! ## The chunk list

`parse_chunks` takes the chunks as a `Vec<Vec<u8>>`; con-leche's `parseChunks`
takes a `List ByteArray`.  The bridge is elementwise. -/

/-- A chunk of the port's parse as con-leche's. -/
def absChunk (c : alloc.vec.Vec Std.U8) : ByteArray := ⟨(c.val.map absByte).toArray⟩

/-- The port's chunk list as con-leche's. -/
def absChunks (cs : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List ByteArray :=
  cs.val.map absChunk

end ConRon.Refine.Frontend

/-
`con-ron-dump` — the differential-testing tool of DESIGN.md §3.6 (task #10).

    lake exe con-ron-dump [--no-check] <export.ndjson> <out.decls>

It runs con-leche's own frontend exactly as `vendor/con-leche/Main.lean` does
before it calls `checkDecls` — the built-in prelude (`Frontend.builtinPreludeE`),
the streaming parse with the in-process `_model` generator on
(`Frontend.parseExportStreamD`), which is where the `NatOpGround` hoist, the
projection rewrite and the prelude dedupe happen — writes the resulting
`List DeclC` in the `con-ron-decls/1` format (`ConRon/Dump/FORMAT.md`), reads it
back with the Lean reader, and checks that

* `parseDecls (dumpDecls ds) = .ok ds'` with `ds'` structurally equal to `ds`
  (the comparison goes through `BEq Expr`, which is con-leche's memoised
  pointer-guarded `Expr.beqMemo`, not the derived `O(tree)` walk), and
* `checkDecls .verified` returns the same verdict on `ds` and on `ds'` — the
  same `isOk`, the same error kind and the same error position.

Exit 0 iff everything agrees, 1 on a mismatch, 2 if the frontend declines or
rejects the stream (reported, never hidden), 3 on an internal or IO failure.
-/
import ConRon.Dump.Read
import ConLeche.Frontend.Prelude
import ConLeche.Cached.Installed

open ConLeche
open ConLeche.Cached
open ConRon.Dump

namespace ConRon.Dump

/-! ## Structural equality of `DeclC`

`DeclC` derives nothing, and the derived `DecidableEq` of `Expr` is the plain
structural walk, which is `O(tree)` on a shared DAG.  These comparisons use
`==`, i.e. `Expr.beq`, which the compiler substitutes by the memoised
pointer-and-hash-guarded `Expr.beqMemo` (`ConLeche/Kernel/Expr.lean`). -/

def cvEq (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

def fireEq : RecRuleFire → RecRuleFire → Bool
  | .inert, .inert => true
  | .plain, .plain => true
  | .nested l₁ p₁, .nested l₂ p₂ => l₁ == l₂ && p₁ == p₂
  | _, _ => false

def ruleEq (a b : RecRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.ctorParams == b.ctorParams
    && fireEq a.fire b.fire && a.rhs == b.rhs && a.k == b.k && a.eta == b.eta
    && a.paramsBlind == b.paramsBlind

def rulesEq : List RecRule → List RecRule → Bool
  | [], [] => true
  | x :: xs, y :: ys => ruleEq x y && rulesEq xs ys
  | _, _ => false

def capsEq (a b : IndCaps) : Bool :=
  a.eta == b.eta && a.etaCtor == b.etaCtor && a.etaParams == b.etaParams
    && a.etaFields == b.etaFields && a.unitlike == b.unitlike
    && a.unitParams == b.unitParams && a.ruleK == b.ruleK
    && a.sortZ == b.sortZ

def tableEq (a b : ProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams
    && a.numParams == b.numParams && a.ctor == b.ctor
    && a.numFields == b.numFields && a.structSort == b.structSort
    && a.bodies == b.bodies && a.guards == b.guards && a.off == b.off

def infoEq : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => cvEq a b
  | .defnInfo a v₁ h₁, .defnInfo b v₂ h₂ => cvEq a b && v₁ == v₂ && h₁ == h₂
  | .thmInfo a v₁, .thmInfo b v₂ => cvEq a b && v₁ == v₂
  | .indInfo a c₁, .indInfo b c₂ => cvEq a b && capsEq c₁ c₂
  | .ctorInfo a p₁ f₁, .ctorInfo b p₂ f₂ => cvEq a b && p₁ == p₂ && f₁ == f₂
  | .recInfo a m₁ r₁ rs₁, .recInfo b m₂ r₂ rs₂ =>
      cvEq a b && m₁ == m₂ && r₁ == r₂ && rulesEq rs₁ rs₂
  | .projInfo t₁, .projInfo t₂ => tableEq t₁ t₂
  | _, _ => false

def infosEq : List ConstantInfo → List ConstantInfo → Bool
  | [], [] => true
  | x :: xs, y :: ys => infoEq x y && infosEq xs ys
  | _, _ => false

def declEq : DeclC → DeclC → Bool
  | .axiomDecl a, .axiomDecl b => cvEq a b
  | .defnDecl a v₁ h₁, .defnDecl b v₂ h₂ => cvEq a b && v₁ == v₂ && h₁ == h₂
  | .thmDecl a v₁, .thmDecl b v₂ => cvEq a b && v₁ == v₂
  | .opaqueDecl a v₁, .opaqueDecl b v₂ => cvEq a b && v₁ == v₂
  | .basisDecl k₁, .basisDecl k₂ => k₁ == k₂
  | .indDecl b₁ n₁, .indDecl b₂ n₂ => n₁ == n₂ && infosEq b₁ b₂
  | _, _ => false

/-- The index of the first differing declaration, if any. -/
def firstDiff (xs ys : List DeclC) : Option Nat :=
  let rec go (i : Nat) : List DeclC → List DeclC → Option Nat
    | [], [] => none
    | x :: xs, y :: ys => if declEq x y then go (i + 1) xs ys else some i
    | _, _ => some i
  go 0 xs ys

/-! ## Verdicts -/

/-- `checkDecls`'s answer, reduced to what the differential test compares:
accept, or the error's kind and the fold position. -/
def verdictStr : Except (CheckError × Nat) Env → String
  | .ok _ => "accept"
  | .error (e, n) =>
    let tag := match e with
      | .notImplemented _ => "notImplemented"
      | .invalid _ => "invalid"
      | .internal _ => "internal"
    tag ++ "@" ++ toString n

/-- con-leche's own exit code for a verdict (`Main.lean`,
`CheckError.exitCode`): 0 accept, 1 reject, 2 decline, 3 internal.  Printed so
that the fixture runner can compare the dump tool against
`tests/*-expected.txt` without re-deriving the mapping. -/
def verdictExit : Except (CheckError × Nat) Env → Nat
  | .ok _ => 0
  | .error (.notImplemented _, _) => 2
  | .error (.invalid _, _) => 1
  | .error (.internal _, _) => 3

end ConRon.Dump

def usage : String :=
  "usage: con-ron-dump [--no-check] <export.ndjson> <out.decls>\n\
   \n\
   Runs con-leche's frontend, writes the parsed `List DeclC` in the\n\
   con-ron-decls/1 format, reads it back and compares (structurally, and\n\
   by the verdict of `checkDecls .verified`)."

def run (inp outp : String) (doCheck : Bool) : IO UInt32 := do
  let prelude ← match Frontend.builtinPreludeE with
    | .ok p => pure p
    | .error (.parseError line msg) => do
      IO.eprintln s!"con-ron-dump: the built-in prelude does not parse (line {line}: {msg})"
      return 3
    | .error (.unsupported what) => do
      IO.eprintln s!"con-ron-dump: the built-in prelude is unsupported ({what})"
      return 3
    | .error (.invalid what) => do
      IO.eprintln s!"con-ron-dump: the built-in prelude contradicts itself ({what})"
      return 3
  let t0 ← IO.monoMsNow
  match ← Frontend.parseExportStreamD inp prelude true false with
  | .error (.unsupported what) => do
    IO.println "  verdict-exit 2"
    IO.eprintln s!"con-ron-dump: DECLINED by the frontend: {what}"
    return 2
  | .error (.invalid what) => do
    IO.println "  verdict-exit 1"
    IO.eprintln s!"con-ron-dump: INVALID stream: {what}"
    return 2
  | .error (.parseError line msg) => do
    IO.println "  verdict-exit 3"
    IO.eprintln s!"con-ron-dump: PARSE ERROR {inp}:{line}: {msg}"
    return 3
  | .ok res => do
    let ds := res.decls.toList
    let tParse ← IO.monoMsNow
    let st := ConRon.Dump.dumpState ds
    let text := ConRon.Dump.joinLines st.buf
    IO.FS.writeFile outp text
    let tWrite ← IO.monoMsNow
    let bytes := text.utf8ByteSize
    match ConRon.Dump.parseDecls text with
    | .error e => do
      IO.eprintln s!"con-ron-dump: FAIL the dump does not read back: {e}"
      return 1
    | .ok ds' => do
      let tRead ← IO.monoMsNow
      let structOk :=
        ds.length == ds'.length && (ConRon.Dump.firstDiff ds ds').isNone
      let redump := ConRon.Dump.dumpDecls ds'
      let byteOk := redump == text
      IO.println s!"con-ron-dump: {inp}"
      IO.println s!"  declarations {st.nD}  names {st.names.size}  levels \
        {st.levels.size}  propwhens {st.pws.size}  exprs {st.exprs.size}"
      IO.println s!"  constvals {st.nV}  recrules {st.nR}  indcaps {st.nC}  \
        projtables {st.nP}  constinfos {st.nI}  lines {st.buf.size}"
      IO.println s!"  bytes {bytes}  parse {tParse - t0}ms  write \
        {tWrite - tParse}ms  read {tRead - tWrite}ms"
      unless structOk do
        IO.eprintln s!"con-ron-dump: FAIL structural mismatch at declaration \
          {ConRon.Dump.firstDiff ds ds'} (lengths {ds.length} vs {ds'.length})"
      unless byteOk do
        IO.eprintln "con-ron-dump: FAIL re-dumping the re-read declarations \
          is not byte-identical"
      if !doCheck then
        IO.println "  checkDecls skipped (--no-check)"
        return (if structOk && byteOk then 0 else 1)
      let r1 := checkDecls .verified ds
      let v1 := ConRon.Dump.verdictStr r1
      let tC1 ← IO.monoMsNow
      let v2 := ConRon.Dump.verdictStr (checkDecls .verified ds')
      let tC2 ← IO.monoMsNow
      IO.println s!"  checkDecls {v1} ({tC1 - tRead}ms) / {v2} ({tC2 - tC1}ms)"
      -- con-leche's driver declines a run in which the frontend skipped a
      -- declaration for a tolerated axiom, *after* an accepting fold
      -- (`Main.lean`, the `taintSkipped.isEmpty` branch).  That is a driver
      -- rule above `checkDecls`, and reproducing it here is what makes the
      -- `verdict-exit` line comparable with `tests/*-expected.txt`.
      let taint := res.taintSkipped.size
      let code := if taint > 0 && ConRon.Dump.verdictExit r1 == 0 then 2
        else ConRon.Dump.verdictExit r1
      if taint > 0 then
        IO.println s!"  taint-skipped {taint}"
      IO.println s!"  verdict-exit {code}"
      let verdictOk := v1 == v2
      unless verdictOk do
        IO.eprintln s!"con-ron-dump: FAIL verdicts differ: {v1} vs {v2}"
      return (if structOk && byteOk && verdictOk then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let doCheck := !args.contains "--no-check"
  match args.filter (fun a => !a.startsWith "--") with
  | [inp, outp] => run inp outp doCheck
  | _ => do IO.eprintln usage; return 3

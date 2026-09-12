/-
`con-ron-dump-pins` — the `Nat`-operation pin dumper (DESIGN.md §3.6's
"pin sets are runtime data" decision, task #31).

    lake exe con-ron-dump-pins [--no-roundtrip] <out.pins>

It writes `ConLeche.natOpPinSets` (`ConLeche/Kernel/NatOpPins.lean:61`, the
plain `List NatOpPinSet` the `#load_natop_pins` command splices out of the
committed `pins/*.json` dumps) in the `con-ron-pins/1` format
(`ConRon/Dump/FORMAT.md` §7), reads it back **in Lean** and checks that

* `parsePins (dumpPins ss) = .ok ss'` with `ss'` equal to `ss` field by field
  (the `Expr` comparisons go through `BEq Expr`, i.e. con-leche's memoised
  pointer-guarded `Expr.beqMemo`, not the derived `O(tree)` walk), and
* re-dumping `ss'` is byte-identical to the file.

There is no `checkDecls` half here: a pin dump is not a declaration list, and
what consumes it is `con-ron-check --pins` on the Rust side.  Exit 0 iff
everything agrees, 1 on a mismatch, 3 on usage or IO failure.

Nothing here is a theorem: this is a test and porting tool.
-/
import ConRon.Dump.Read
import ConLeche.Kernel.NatOpPins

open ConLeche
open ConRon.Dump

namespace ConRon.Dump

/-! ## Structural equality of `NatOpPinSet`

`NatOpPinSet` derives nothing, and the derived `DecidableEq` of `Expr` is the
plain structural walk, which is `O(tree)` on a shared DAG — and a pin variant
is a 20 000-node DAG whose tree expansion is 5.1 M nodes (DESIGN.md task #22).
These comparisons use `==`, i.e. `Expr.beq`, which the compiler substitutes by
the memoised pointer-and-hash-guarded `Expr.beqMemo`. -/

/-- Two pin variants, field by field. -/
def pinSetEq (a b : NatOpPinSet) : Bool :=
  a.toolchain == b.toolchain
    && a.divPin == b.divPin && a.modPin == b.modPin
    && a.gcdPin == b.gcdPin && a.landPin == b.landPin
    && a.lorPin == b.lorPin && a.xorPin == b.xorPin
    && a.shiftLeftPin == b.shiftLeftPin && a.shiftRightPin == b.shiftRightPin
    && a.divProofs == b.divProofs && a.modProofs == b.modProofs
    && a.gcdProofs == b.gcdProofs && a.landProofs == b.landProofs
    && a.lorProofs == b.lorProofs && a.xorProofs == b.xorProofs
    && a.shiftLeftProofs == b.shiftLeftProofs
    && a.shiftRightProofs == b.shiftRightProofs

/-- The index of the first differing variant, if any. -/
def firstPinDiff (xs ys : List NatOpPinSet) : Option Nat :=
  let rec go (i : Nat) : List NatOpPinSet → List NatOpPinSet → Option Nat
    | [], [] => none
    | x :: xs, y :: ys => if pinSetEq x y then go (i + 1) xs ys else some i
    | _, _ => some i
  go 0 xs ys

/-- The proof-blob counts of one variant, in the field order of the record:
the census `--no-roundtrip` prints and `tests/pindump.sh`'s freshness check
would compare. -/
def proofCounts (s : NatOpPinSet) : List Nat :=
  [s.divProofs.length, s.modProofs.length, s.gcdProofs.length,
   s.landProofs.length, s.lorProofs.length, s.xorProofs.length,
   s.shiftLeftProofs.length, s.shiftRightProofs.length]

end ConRon.Dump

def usage : String :=
  "usage: con-ron-dump-pins [--no-roundtrip] <out.pins>\n\
   \n\
   Writes `ConLeche.natOpPinSets` in the con-ron-pins/1 format\n\
   (proof/ConRon/Dump/FORMAT.md §7), reads it back and compares.\n\
   \n\
   --no-roundtrip   write the file and stop"

def run (outp : String) (doRoundTrip : Bool) : IO UInt32 := do
  let ss := ConLeche.natOpPinSets
  let t0 ← IO.monoMsNow
  let st := ConRon.Dump.dumpPinsState ss
  let text := ConRon.Dump.joinLines st.buf
  IO.FS.writeFile outp text
  let tWrite ← IO.monoMsNow
  let bytes := text.utf8ByteSize
  IO.println s!"con-ron-dump-pins: {outp}"
  IO.println s!"  pin sets {st.nS}  names {st.names.size}  levels \
    {st.levels.size}  propwhens {st.pws.size}  exprs {st.exprs.size}"
  IO.println s!"  lines {st.buf.size}  bytes {bytes}  write {tWrite - t0}ms"
  for s in ss do
    IO.println s!"  variant {s.toolchain}  proof blobs {ConRon.Dump.proofCounts s}"
  if !doRoundTrip then
    IO.println "  round trip skipped (--no-roundtrip)"
    return 0
  match ConRon.Dump.parsePins text with
  | .error e => do
    IO.eprintln s!"con-ron-dump-pins: FAIL the dump does not read back: {e}"
    return 1
  | .ok ss' => do
    let tRead ← IO.monoMsNow
    let structOk :=
      ss.length == ss'.length && (ConRon.Dump.firstPinDiff ss ss').isNone
    let redump := ConRon.Dump.dumpPins ss'
    let byteOk := redump == text
    IO.println s!"  read {tRead - tWrite}ms"
    unless structOk do
      IO.eprintln s!"con-ron-dump-pins: FAIL structural mismatch at variant \
        {ConRon.Dump.firstPinDiff ss ss'} (lengths {ss.length} vs {ss'.length})"
    unless byteOk do
      IO.eprintln "con-ron-dump-pins: FAIL re-dumping the re-read variants is \
        not byte-identical"
    if structOk && byteOk then
      IO.println "  round trip exact"
      return 0
    else
      return 1

def main (args : List String) : IO UInt32 := do
  let doRoundTrip := !args.contains "--no-roundtrip"
  match args.filter (fun a => !a.startsWith "--") with
  | [outp] => run outp doRoundTrip
  | _ => do IO.eprintln usage; return 3

#!/usr/bin/env python3
"""scripts/arena-census.py — THE ARENA PROGRESS CENSUS (task #97-CENSUS).

`scripts/progress.py` is the OLD tower's report: it credits a con-leche
declaration when some Rust item cites it and when `Refine/<M>.lean` states
that item's `f_refines`.  The arena rewrite (DESIGN.md §8) has neither of
those trees — `ConRon/Refine/**` is retired and the thing being proved is no
longer "the Rust against con-leche" but TWO theorems with the Lean twin in
the middle:

    (A) con-leche, pure   <--  Theorem 1 (Bridge)  --  (B) the Lean twin
    (B) the Lean twin     <--  Theorem 2 (Refine2) --  (C) the Rust

So the arena needs its own ledger, and its unit is **the twin**: one
top-level definition of `proof/ConRon/Arena/**`.  For each one this script
asks the two questions the coordinator hands work out by, from the SOURCE
TREE ALONE — python3 stdlib, no build, milliseconds, exactly as
`scripts/twin-lines.py` does (whose `Lean twin:` parser this reuses):

  **T1 (the bridge, B ⇒ A)** — does `proof/ConRon/Bridge/**` contain a
  top-level `theorem` about this twin, and is its block free of `sorry`?

  **T2 (the refinement, C ⇒ B)** — which Rust function cites this twin as
  its `Lean twin:`, does `proof/ConRon/Refine2/**` state that function's
  `<rust_fn>_refines`, and is its block free of `sorry`?

Nothing here is a gate.  A census that can FAIL is a census people learn to
route around; this one only ever reports, and `scripts/gates.sh` prints its
`--summary` beside `progress.py`'s.

--------------------------------------------------------------- the unit

A twin is a top-level `def` (`partial def` included) of
`proof/ConRon/Arena/**` **under its enclosing `namespace`s**, mutual-block
members included (they sit at column 0 and `provenance.top_level_decls`
already sees them).  The namespace is not decoration: `Arena/Store.lean`
declares `dropScratch` FOUR times, once inside each of `NStore`, `LStore`,
`LsStore` and `EStore`, and nine `empty`s and nine `find?`s the same way.
Round 1 keyed a row by `(file, declared name)` and silently collapsed 88
definitions into 21 rows; round 2 tracks `namespace`/`section`/`mutual`/`end`
and keys by the qualified name, so the census gained the 67 twins that were
being hidden (1 565 → 1 632).

NOT `theorem`s (the arena's own verification is not a thing the bridge
restates), NOT `structure` / `inductive` / `class` / `instance` (a type is
mirrored by the denotation, not by a theorem about a function), and NOT
`abbrev` — the arena's 33 are type synonyms (`abbrev EIdx := Idx .expr`, `abbrev AM :=
StateT AState (Except CheckError)`) and `@f` aliases of a `def` that is
already a row (`abbrev checkSumTeleF := @checkSumTele`), neither of which is
a second obligation.

**Arms belong to their dispatcher.**  Task #97-P3-1 split each walk into a
dispatcher and one `def` per constructor arm, and task #97-TWIN's rule is
that ONE Rust function cites the DISPATCHER: "the arms are the twin's own
shape (a Lean proof obligation per arm), not a second ledger the Rust has to
mirror."  This script follows that rule in both directions.  An arm — a def
whose name matches `Arm[A-Z]` and which exactly one non-arm definition of
the same file mentions — contributes NO row of its own; it is listed in its
dispatcher's row, its own bridge theorems (some arms have one, e.g.
`instantiate1ArmApp_spec`) count toward the dispatcher's T1, and a `sorry`
in any of them un-closes the dispatcher.  An `Arm[A-Z]` definition with no
unique owner keeps its own row, and the self-check line says how many.

--------------------------------------------------- the T1 conventions

Discovered by sampling every `theorem` of `proof/ConRon/Bridge/**` against
every definition of `proof/ConRon/Arena/**` and reading off the suffixes
that occur.  A theorem is ABOUT twin `X` when its name is `X` plus one of:

    _spec       the Hoare-triple statement, `⦃fun s => ⌜s = s₀⌝⦄ X … ⦃…⦄`
                — the tier's main shape and 373 of the matches;
    _spec'      a second spelling of the same (`internBindIE_spec'`);
    _specV      the value-flavoured answer (`internE_specV`, `RelV`);
    _specI      the invariant-carrying spelling (`abs1Set_specI`);
    _specG      the generic/`grind` spelling (`liftSet_specG`);
    _specF      the fuel-parameterised spelling (`readLevelM_specF`);
    _run        the run-form statement, `X … s = .ok (r, s') → …`
                (`allLevelParamsDefined_run`) — the shape a pure or
                state-preserving twin gets instead of a triple;
    _bridge     DESIGN §8.2's own name for the per-declaration join point
                (`checkDecl_bridge`), and its per-constructor refinements
                `_bridge_defn` / `_bridge_thm` / `_bridge_ind` / …;
    _exact      the frontend tier's exactness statement
                (`exprPtrBEq_exact`).

`X` may be written with or without a namespace on either side, the way
`provenance.names_compatible` allows: `EStore.viewApp` answers to
`viewApp_spec` and to `EStore.viewApp_spec` alike.

**One theorem credits ONE twin** (round 2).  Round 1 matched on the LEAF
name alone, so `Bridge/Specs.lean`'s `viewApp_spec` was credited to both
`Monad.lean`'s `viewApp` and `Store.lean`'s `EStore.viewApp`, and
`Promote/StoreP.lean`'s `EStore.internPersistent_spec` to all four
`*Store.internPersistent` — 31 theorems double-counted.  `t1_candidates`
ranks the candidates and takes the best: the LONGEST twin leaf first
(`EIdx_hasLevelParam_spec` is `hasLevelParam`'s, not `EIdx`'s), then the
namespace (`ns_rank` — same namespace beats one that drops the other's, and
an INCOMPATIBLE namespace is not a candidate at all, which is how
`Inst1LAt.bvar_down` stops being read as a lemma about `ETag.bvar`), then
the Bridge module's own tier as the tiebreak
(`Bridge/Frontend/Shared.lean`'s `internExpr_run` is
`Frontend/Readback.lean`'s `internExpr`, not `Intern.lean`'s).  A theorem
whose two best candidates still tie is reported as AMBIGUOUS.

Every OTHER `X…` theorem name — `_ext`, `_pext`, `_step`, `_of_not_lam`,
`_leaf`, … — is a side lemma, not the statement, and does NOT count as
"stated".  But it is not thrown away either: a twin whose only match is an
unrecognised suffix is counted and listed in the self-check line, so a
convention this script does not know cannot pass silently as "unstated".

**The escape hatch is the doc comment.**  A statement whose NAME is none of
the above can say so in its own `/-- … -/` block: ``Theorem 1 for `X` ``
(any case — `ExprOps/InstLP.lean`'s `substLevelList_eq` shouts it) names the
twin outright, and the theorem is credited to it.  Eight theorems over six
twins use it at the tip, and it is consulted only where the name gives no
recognised suffix — so `instantiateListFast_spec`, whose doc says "THEOREM 1
for `instantiateList`, at the entry point", keeps crediting the twin it is
literally about.  Round 2's hand triage of the remaining 52 rows put 25 of
them in the "IS the statement, under another name" class and 27 in the "side
lemma that merely mentions the twin" class; the 25 are a doc line their
tier's owner can add, not a script change.

--------------------------------------------------- the T2 conventions

The `Lean twin:` line is the arrow from the Rust to the twin, and
`scripts/twin-lines.py`'s parser is what reads it (one parser, one set of
rules — the same argument that file makes about `provenance.py`).  A
citation sits in the doc block of the Rust item just below it; the item's
`fn` name is the T2 subject.  `proof/ConRon/Refine2/**` then states

    <rust_fn>_refines     the refinement lemma (938 credits at the tip), or
    <rust_fn>_no_claim    the "this arm claims nothing" lemma, which counts
                          as stated AND closed, flagged `N` in the table — a
                          `Native` decline or an error constructor the port
                          deliberately does not model;
    <rust_fn>_abs         the ABSTRACTION shape, `Refine2/AbsStore.lean` and
    <rust_fn>_run         `Refine2/Specs.lean`'s "inversion layer keyed on
    <rust_fn>_obs         the Rust equation" (task #97-P5-2): `arena.monad
                          .view_app pers st h = ok o → …` with the twin's
                          answer on the right.  That IS the store and core
                          tiers' Theorem 2 statement — `derived_e_run`,
                          `word_index_abs`, `der_of_bvar_obs` — and round 1
                          did not know it, which is why the `Store` row's T2
                          column read `6/315`.  `_abs` is the pure
                          abstraction equation, `_run` the monadic run form,
                          `_obs` the up-to-`derObsE` form the derived-word
                          arms need.

**The receiver qualifies the name.**  `provenance.RustItem.name()` is the
BARE `fn` name, so `Tbl::find`, `ETables::find` and `EStore::find` are all
`find`, while `Refine2/**` writes `tbl_find_abs`, `etables_find_abs`,
`estore_find_abs`.  `with_impl` reads each `fn`'s enclosing `impl` block and
offers `<receiver>_<fn>` as a FALLBACK key, in both spellings the tier uses
(`etables_…` and `e_tables_…`).  That is finding (4) on the refinement side,
and it moved 42 rows out of "named by a theorem under another shape".

A twin cited by several Rust functions (a store projection is cited from
four call sites) needs one `_refines` EACH: the row is `T2 stated` only when
every citing function has one, and `--open` names the ones that do not.

**The citation is resolved by NAME, then by range.**  `twin-lines.py update`
relocates a citation by name and rewrites only its digits, so the name is the
authority: `store.rs`'s `EStore.find?` is `EStore`'s `find?` even where the
citation's range has rotted onto `Tbl.find?` (which `twin-lines.py check`
accepts, because `provenance.locate_decl` is namespace-blind).  The cited
RANGE is the tiebreak, and it is what settles an UNQUALIFIED citation of one
of `Arena/Store.lean`'s four `dropScratch`.

------------------------------------------------------------- the skips

A twin that needs no bridge theorem needs a LISTED REASON, the way
`scripts/provenance-skip.txt` lists the con-leche declarations the Rust port
does not carry.  `scripts/arena-census-skip.txt` is that list:

    <proof-relative Lean path> <decl|*> <T1|T2|BOTH> <reason>

so "not stated" is never silent.  A skip that names no definition of its
file is reported as STALE, and a skip whose twin turns out to be stated
anyway as REDUNDANT — the list cannot rot quietly either.

------------------------------------------------------------- the output

    (default)   the per-twin table, sorted by tier then file then line
    --summary   one line per tier plus totals (what `gates.sh` prints)
    --md        the same table as Markdown, for DESIGN.md
    --open      only the rows with something missing, GROUPED BY what is
                missing — the work list the coordinator hands out
    --selftest  run the whole census over `scripts/testdata/arena-census/`,
                a twenty-six-row miniature of the real tree, and compare
                both the per-row verdicts and the self-check COUNTS with
                the committed `expected.txt`

Exit code 0 always, except `--selftest` (1 on a mismatch) and 2 for a usage
or IO error.  `--open` and the rest never fail: this is a REPORT.
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)

ARENA_DIR = "proof/ConRon/Arena"
BRIDGE_DIR = "proof/ConRon/Bridge"
REFINE2_DIR = "proof/ConRon/Refine2"
SKIP_FILE = "scripts/arena-census-skip.txt"
FIXTURE = os.path.join(HERE, "testdata", "arena-census")

DEF_KW = ("def",)

# The suffixes that make a Bridge theorem THE statement about a twin, in the
# order the docstring lists them.  `_bridge` is a prefix match (its
# per-constructor refinements append another tag).
T1_SUFFIXES = ("_spec", "_spec'", "_specV", "_specI", "_specG", "_specF",
               "_run", "_exact")
T1_PREFIX_SUFFIXES = ("_bridge",)

# The Refine2 shapes that ARE a Rust function's Theorem 2 statement, keyed by
# the tier that writes them — see the docstring's "the T2 conventions".
T2_SUFFIXES = (("_refines", False), ("_no_claim", True),
               ("_abs", False), ("_run", False), ("_obs", False))

# `Theorem 1 for `X`` in a Bridge theorem's OWN doc comment: the escape hatch
# for a statement whose name is not one of the T1 suffixes.  Six theorems use
# it at the tip, over four twins (`eidxCopyUpto`, `takeEidx`, `lastEidx`,
# `substLevelList`) — case-insensitive, because `substLevelList_eq` shouts it
# ("**THEOREM 1 for `substLevelList`**").
T1_DOC_RE = re.compile(r"theorem 1 for\s+\*{0,2}`([A-Za-z0-9_.']+)`", re.I)

ARM_RE = re.compile(r"Arm[A-Z]")
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")

# Namespace tracking, so that `Store.lean`'s four `dropScratch` are four twins
# and `EStore.viewApp` is not `Monad.lean`'s `viewApp`.
NS_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
SECTION_RE = re.compile(r"^(section|mutual)\b")
END_RE = re.compile(r"^end\b\s*([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)?")

# The namespace components that are the TREE and not the twin.  A module's
# own path is the first cut — `Bridge/Inductives/SumInstall.lean` opens
# `namespace ConRon.Bridge.Inductives`, and `majorIdx_spec` there must compare
# against `Arena/SumInstall.lean`'s `InductiveShape.majorIdx` as
# `majorIdx_spec`, not as `Inductives.majorIdx_spec` — and `ROOT_NS` is the
# second, because a Bridge file may open `namespace ConRon.Arena` and spell a
# theorem `Arena.checkDeclsPure_bridge`.
ROOT_NS = ("ConRon", "Arena", "Bridge", "Refine2")


def strip_root(name, path=None):
    """The census name: `ConRon.Arena.EStore.viewApp` → `EStore.viewApp`.

    `path` is the declaring module, repo-relative; the components its own
    dotted path contributes are dropped first, then any leading `ROOT_NS`."""
    parts = name.split(".")
    i = 0
    if path:
        mod = path[len("proof/"):-len(".lean")].split("/") \
            if path.startswith("proof/") else path[:-len(".lean")].split("/")
        while i < len(parts) - 1 and i < len(mod) and parts[i] == mod[i]:
            i += 1
    while i < len(parts) - 1 and parts[i] in ROOT_NS:
        i += 1
    return ".".join(parts[i:])


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


P = _load("provenance", os.path.join(HERE, "provenance.py"))
T = _load("twinlines", os.path.join(HERE, "twin-lines.py"))


# ------------------------------------------------------------------- tiers

# A twin's TIER is the round of DESIGN §8.6 that owns it, which is also the
# subdirectory of `Bridge/` and `Refine2/` its theorems live in.  The table
# is explicit so that a NEW arena module gets a tier line of its own rather
# than joining a wrong one silently: anything unlisted falls back to its own
# module path, which is loud.
TIERS = (
    ("Store",      ("Handle", "Store", "Intern", "WF", "WFProofs", "Denote",
                    "Monad", "PropRead")),
    ("ExprOps",    ("ExprOps",)),
    ("Core",       ("Core", "CoreState", "CoreGated", "CoreIO")),
    ("Checker",    ("Checker", "CheckerBase", "CheckerSplit", "CheckerGated",
                    "DeclCheck", "Canon", "Pins", "Basis", "NatOpPinSet",
                    "StdAxioms", "TrustAxioms", "Env", "FEnv")),
    ("Inductives", ("Inductives",)),
    ("Frontend",   ("Frontend",)),
    ("Promote",    ("Promote", "PromoteExt")),
    ("Driver",     ("Main", "Bench")),
    ("Tests",      ("StoreTest", "ExprOpsTest", "CoreTest", "CheckerTest",
                    "InductivesTest", "Frontend/ProjRecTest")),
)
TIER_ORDER = [name for name, _ in TIERS] + ["?"]


def tier_of(path):
    """`path` is repo-relative (`proof/ConRon/Arena/Frontend/ExportC.lean`)."""
    stem = path[len(ARENA_DIR) + 1:-len(".lean")]
    head = stem.split("/")[0]
    for name, members in TIERS:
        if stem in members or head in members:
            return name
    return "?" + stem


def tier_of_bridge(path):
    """The tier a `Bridge/**` (or `Refine2/**`) module belongs to, read off
    its own subdirectory: `Bridge/Frontend/Shared.lean` is `Frontend`.

    Only a TIEBREAK — when two twins are equally good candidates for one
    theorem, the one in the theorem's own tier wins."""
    stem = path.split("/")
    for i, part in enumerate(stem):
        if part in ("Bridge", "Refine2") and i + 1 < len(stem):
            head = stem[i + 1][:-len(".lean")] \
                if stem[i + 1].endswith(".lean") else stem[i + 1]
            for name, members in TIERS:
                if head in members:
                    return name
            return None
    return None


# ------------------------------------------------------------------- input

def lean_files(root, sub):
    base = os.path.join(root, sub)
    out = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = sorted(dirnames)
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                out.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return sorted(out)


_FILE_CACHE = {}


def file_lines(root, path):
    """The file's lines, cached by path.

    Not only for speed: `scripts/twin-lines.py` memoises
    `provenance.comment_lines` on `(id(lines), len(lines))`, and importing it
    installs that wrapper here too — so a lines list that is garbage-collected
    can have its id reused by another list of the same length and collide.
    Holding every file's lines for the run makes the key stable."""
    key = (root, path)
    if key not in _FILE_CACHE:
        with open(os.path.join(root, path), encoding="utf-8") as f:
            _FILE_CACHE[key] = f.read().split("\n")
    return _FILE_CACHE[key]


class Decl:
    """One top-level declaration, with its block and whether it is proved.

    `name` is the name as WRITTEN (`dropScratch`); `full` is that name under
    the enclosing `namespace`s with the tree's own root stripped
    (`EStore.dropScratch`).  Every comparison this script makes is on `full`:
    `Arena/Store.lean` declares `dropScratch` four times, once in each of
    `NStore`/`LStore`/`LsStore`/`EStore`, and they are four twins."""

    def __init__(self, path, lineno, kw, name, a, b, has_sorry, ns=()):
        self.path = path
        self.lineno = lineno
        self.kw = kw
        self.name = name
        self.a = a
        self.b = b
        self.has_sorry = has_sorry
        self.full = strip_root(".".join(list(ns) + [name]), path)
        parts = self.full.split(".")
        self.ns = tuple(parts[:-1])
        self.leaf = parts[-1]


def block_has_sorry(lines, skip, a, b):
    """Is there a `sorry` TOKEN in the 1-based block `(a, b)`?

    Comments do not count: `ExprOps/Owed.lean` says "every one is `sorry`" in
    its module docstring, and a doc comment is not a proof.  Block comments
    come from `provenance.comment_lines` (which the `/- … -/` nesting needs)
    and are computed ONCE per file by the caller — `comment_lines` scans
    character by character, and calling it per declaration is 25 of this
    script's 26 seconds; `--` line comments are cut here."""
    for i in range(a - 1, min(b, len(lines))):
        if i in skip:
            continue
        text = lines[i].split("--")[0]
        if SORRY_RE.search(text):
            return True
    return False


def namespace_at(lines, skip):
    """{0-based line -> the enclosing namespace, as a tuple of components}.

    A `section` — and a `mutual`, of which `Arena/ExprOps.lean` has 23 —
    contributes nothing to the NAME but has to be tracked, because its bare
    `end` would otherwise close the enclosing namespace; `end X` closes the
    entry it names.  Only column-0 lines count, and comment lines are cut,
    exactly as `top_level_decls` reads its declarations."""
    out = {}
    stack = []            # [(name-or-None, parts)]
    for i, line in enumerate(lines):
        if i in skip or not line or line[:1].isspace():
            out[i] = tuple(p for _, ps in stack for p in ps)
            continue
        m = NS_RE.match(line)
        if m:
            stack.append((m.group(1), tuple(m.group(1).split("."))))
        elif SECTION_RE.match(line):
            stack.append((None, ()))
        else:
            m = END_RE.match(line)
            if m and stack:
                want = m.group(1)
                for j in range(len(stack) - 1, -1, -1):
                    if stack[j][0] == want:
                        del stack[j:]
                        break
                else:
                    stack.pop()
        out[i] = tuple(p for _, ps in stack for p in ps)
    return out


def scan_decls(root, sub, kws):
    """Every top-level declaration of `<root>/<sub>/**` whose keyword is in
    `kws`, as `Decl`s, in file then line order."""
    out = []
    for path in lean_files(root, sub):
        lines = file_lines(root, path)
        skip = P.comment_lines(lines)
        ns = namespace_at(lines, skip)
        for lineno, kw, name in P.top_level_decls(lines):
            if kw not in kws:
                continue
            a, b = P.extend_block(lines, lineno - 1)
            out.append(Decl(path, lineno, kw, name, a, b,
                            block_has_sorry(lines, skip, a, b),
                            ns.get(lineno - 1, ())))
    return out


# ------------------------------------------------------------------- skips

def load_skips(root):
    """({(path, decl): (scope, reason)}, malformed lines).

    `<path> <decl|*> <T1|T2|BOTH> <reason>`; the reason is mandatory, as in
    `scripts/provenance-skip.txt`."""
    skips, bad = {}, []
    full = os.path.join(root, SKIP_FILE)
    if not os.path.exists(full):
        return skips, bad
    with open(full, encoding="utf-8") as f:
        for i, raw in enumerate(f):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 3)
            if len(parts) < 4 or parts[2] not in ("T1", "T2", "BOTH") \
                    or not parts[3].strip():
                bad.append((i + 1, line))
                continue
            path, decl, scope, reason = parts[0], parts[1], parts[2], parts[3]
            if (path, decl) in skips:
                bad.append((i + 1, line + "  [duplicate]"))
                continue
            skips[(path, decl)] = (scope, reason.strip())
    return skips, bad


def skip_for(skips, path, name):
    return skips.get((path, name)) or skips.get((path, "*"))


# ------------------------------------------------------------------ the T1

def ns_rank(thm_ns, twin_ns):
    """How well the theorem's namespace matches the twin's: 0 the SAME, 1 one
    of them drops the other's (a `Bridge` file that does not reopen `EStore`,
    or one that writes `Arena.checkDeclsPure_bridge`), None incompatible.

    `Inst1LAt.bvar_down` is `ExprOps/Subst.lean`'s lemma about the `bvar` case
    of the `Inst1L` relation, NOT a side lemma of `Handle.lean`'s `ETag.bvar`:
    two different namespaces, neither a suffix of the other, so it is not
    attributed to that twin at all."""
    if thm_ns == twin_ns:
        return 0
    n = min(len(thm_ns), len(twin_ns))
    if thm_ns[len(thm_ns) - n:] == twin_ns[len(twin_ns) - n:]:
        return 1
    return None


def t1_tag(thm_leaf, twin_leaf):
    """The tag `thm_leaf` appends to `twin_leaf`, or None if it does not.

    `''` for an exact match, `_spec` for `viewApp_spec`, `'` for a primed
    second spelling."""
    if thm_leaf == twin_leaf:
        return ""
    for sep in ("_", "'"):
        if thm_leaf.startswith(twin_leaf + sep):
            return thm_leaf[len(twin_leaf):]
    return None


def t1_recognised(tag):
    """Is `tag` one of the T1 conventions — i.e. IS this theorem the twin's
    Theorem 1 statement, rather than a side lemma about it?"""
    if tag in T1_SUFFIXES:
        return True
    for suf in T1_PREFIX_SUFFIXES:
        if tag.startswith(suf):
            return True
    return False


def t1_candidates(thm, twins):
    """[(rank, twin)] for every twin Bridge theorem `thm` could be about.

    `rank` orders the candidates so that exactly ONE wins (the caller takes
    the best and reports the rest): the LONGEST twin leaf first — the short
    names are prefixes of the long ones and `EIdx_hasLevelParam_spec` is
    `hasLevelParam`'s statement, not `EIdx`'s — then the namespace match, so
    `viewApp_spec` is `Monad.lean`'s `viewApp` (same namespace) and not
    `Store.lean`'s `EStore.viewApp` (the theorem would have to drop a
    namespace), and `EStore.internPersistent_spec` is `EStore`'s of the four
    `*Store.internPersistent`."""
    out = []
    for twin in twins:
        tag = t1_tag(thm.leaf, twin.leaf)
        if tag is None:
            continue
        r = ns_rank(thm.ns, twin.ns)
        if r is None:
            continue
        out.append(((-len(twin.leaf), r), twin, tag))
    return out


IMPL_RE = re.compile(r"^impl\b(?:\s*<[^>]*>)?\s+(?:.+\s+for\s+)?"
                     r"([A-Za-z_][A-Za-z0-9_]*)")


def receiver_spellings(name):
    """How `Refine2/**` writes the receiver type in a qualified lemma name.

    TWO spellings are in use and both are tried: the flat lowercase
    (`ETables` → `etables_get_abs`, `EStore` → `estore_view_abs`, the tier's
    own habit) and the snake case Charon gives an item (`ETables` →
    `e_tables`).  A qualified name is only ever a FALLBACK key, so offering
    both costs a dict lookup."""
    s = re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", name)
    s = re.sub(r"([A-Z]+)(?=[A-Z][a-z])", r"\1_", s)
    out = [name.lower()]
    if s.lower() != out[0]:
        out.append(s.lower())
    return out


def with_impl(path, items):
    """[(item, `<impl type>_<fn>` or None)] over one file's Rust items.

    `provenance.RustItem.name()` is the BARE name, so `Tbl::find`,
    `ETables::find` and `EStore::find` are all `find` — and the Refine2 tier
    qualifies by receiver (`tbl_find_abs`, `etables_find_abs`,
    `estore_find_abs`).  Without the qualification `Tbl.find?` and
    `ETables.find?` would share one T2 verdict, which is task #97-CENSUS
    round 2's finding (4) on the refinement side.

    An `impl` block runs from its own column-0 `impl` line to the next
    column-0 `}`, which is what `rustfmt` guarantees and what keeps a free
    function after the block from inheriting the receiver.  The qualified name
    is only ever a FALLBACK key, so a mis-read would cost a lookup, not a
    verdict."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    spans = []
    for n, line in enumerate(lines, 1):
        m = IMPL_RE.match(line)
        if not m:
            continue
        end = len(lines)
        for k in range(n, len(lines)):
            if lines[k].startswith("}"):
                end = k + 1
                break
        spans.append((n, end, receiver_spellings(m.group(1))))
    out = []
    for i in sorted(items, key=lambda i: i.lineno):
        q = ()
        if i.kind == "fn":
            for a, b, tys in spans:
                if a < i.lineno <= b:
                    q = tuple(ty + "_" + i.name() for ty in tys)
                    break
        out.append((i, q))
    return out


def mentions_fn(thm, fn):
    """Does Refine2 theorem `thm` name Rust function `fn` anywhere in it?

    The T2 self-check's predicate, and deliberately loose: the store tier's
    lemmas are `estore_view_app_abs`, not `view_app_refines`, and a census
    that reported those twins as "nothing stated" without saying that a
    theorem naming the function exists would be misleading.  `_`-delimited,
    so `view` does not match `view_app`."""
    return thm == fn or thm.startswith(fn + "_") or thm.endswith("_" + fn) \
        or ("_" + fn + "_") in thm


# ---------------------------------------------------------------- the rows

class Row:
    def __init__(self, d, tier):
        self.d = d
        self.tier = tier
        self.arms = []            # [Decl]
        self.t1 = []              # [(Decl, suffix)]
        self.t1_other = []        # [Decl] — an unrecognised suffix
        self.rust = []            # [(fn name, rust file, twin citation line)]
        self.qual = {}            # fn name -> the `<impl type>_<fn>` spellings
        self.t2 = {}              # fn name -> (Decl, is_no_claim) or None
        self.t2_other = []        # Refine2 theorem names under another shape
        self.skip = None          # (scope, reason)

    # --- T1
    @property
    def t1_skipped(self):
        return self.skip is not None and self.skip[0] in ("T1", "BOTH")

    @property
    def t1_stated(self):
        return bool(self.t1)

    @property
    def t1_closed(self):
        return bool(self.t1) and not any(t.has_sorry for t, _ in self.t1)

    # --- T2
    @property
    def t2_skipped(self):
        return self.skip is not None and self.skip[0] in ("T2", "BOTH")

    @property
    def t2_cited(self):
        return bool(self.rust)

    @property
    def t2_stated(self):
        return bool(self.rust) and all(self.t2.get(f) for f, _, _ in self.rust)

    @property
    def t2_closed(self):
        if not self.t2_stated:
            return False
        for f, _, _ in self.rust:
            d, no_claim = self.t2[f]
            if d.has_sorry:
                return False
        return True

    def t1_cell(self):
        if self.t1_skipped:
            return "-", "(skip)"
        if not self.t1:
            return ".", "!" if self.t1_other else ""
        name = self.t1[0][0].name
        if len(self.t1) > 1:
            name += " +%d" % (len(self.t1) - 1)
        return ("closed" if self.t1_closed else "sorry"), name

    def t2_cell(self):
        if self.t2_skipped:
            return "-", "(skip)"
        if not self.rust:
            return ".", ""
        fns = [f for f, _, _ in self.rust]
        got = [f for f in fns if self.t2.get(f)]
        if not got:
            return ".", fns[0] + (" +%d" % (len(fns) - 1) if len(fns) > 1 else "")
        d, no_claim = self.t2[got[0]]
        name = d.name + ("(N)" if no_claim else "")
        if len(got) < len(fns):
            # SOME of the citing functions have a lemma: neither "stated"
            # (the twin's refinement is not covered) nor "nothing there".
            return "part", name + " [%d/%d]" % (len(got), len(fns))
        if len(got) > 1:
            name += " +%d" % (len(got) - 1)
        return ("closed" if self.t2_closed else "sorry"), name


# -------------------------------------------------------------- the census

class Census:
    def __init__(self, root):
        self.root = root
        self.rows = []
        self.orphan_arms = []
        self.skip_bad = []
        self.skip_stale = []
        self.skip_redundant = []
        # a `Lean twin:` line on a `struct`/`const`/`impl` rather than a `fn`
        self.non_fn_citations = 0
        self.all_rust_fns = set()
        self.build()

    # -- the twins, and which of them are arms
    def build(self):
        root = self.root
        defs = scan_decls(root, ARENA_DIR, DEF_KW)
        by_file = collections.defaultdict(list)
        for d in defs:
            by_file[d.path].append(d)

        owner = {}
        for path, ds in by_file.items():
            arms = [d for d in ds if ARM_RE.search(d.leaf)]
            if not arms:
                continue
            lines = file_lines(root, path)
            others = [d for d in ds if not ARM_RE.search(d.leaf)]
            bodies = [(o, "\n".join(lines[o.a - 1:o.b])) for o in others]
            for arm in arms:
                pat = re.compile(r"(?<![A-Za-z0-9_'.])"
                                 + re.escape(arm.leaf)
                                 + r"(?![A-Za-z0-9_'])")
                hits = [o for o, body in bodies if pat.search(body)]
                if len(hits) == 1:
                    owner[(path, arm.full)] = hits[0].full
                else:
                    self.orphan_arms.append(arm)

        rows = {}
        for d in defs:
            if (d.path, d.full) in owner:
                continue
            key = (d.path, d.full)
            # `Main.lean` declares `main` twice, once inside `namespace
            # ConRon.Arena` and once at the root as its `@[main]` entry point:
            # two definitions, two rows, and the line settles the key.
            if key in rows:
                key = (d.path, "%s#%d" % (d.full, d.lineno))
            rows[key] = Row(d, tier_of(d.path))
        for d in defs:
            key = owner.get((d.path, d.full))
            if key is not None and (d.path, key) in rows:
                rows[(d.path, key)].arms.append(d)
        self.rows = list(rows.values())
        self.by_key = rows

        # -- the skips
        skips, self.skip_bad = load_skips(root)
        names = collections.defaultdict(set)
        for d in defs:
            names[d.path].add(d.name)
            names[d.path].add(d.full)
        for (path, decl), (scope, reason) in sorted(skips.items()):
            if path not in names:
                self.skip_stale.append((path, decl, "no such arena module"))
            elif decl != "*" and decl not in names[path]:
                self.skip_stale.append((path, decl, "no such definition"))
        for r in self.rows:
            s = skip_for(skips, r.d.path, r.d.full) \
                or skip_for(skips, r.d.path, r.d.name)
            if s:
                r.skip = s

        # -- T1: the Bridge theorems
        #
        # ONE THEOREM CREDITS ONE TWIN.  A theorem is attributed to the best
        # candidate of `t1_candidates` — longest twin leaf, then the closest
        # namespace — with the Bridge module's own tier as the tiebreak, so
        # `Bridge/Frontend/Shared.lean`'s `internExpr_run` is
        # `Frontend/Readback.lean`'s `internExpr` and not `Intern.lean`'s.
        # Before task #97-CENSUS round 2 a theorem could be credited to
        # several twins at once (31 were), which inflated both `T1 stated`
        # and the unrecognised-suffix list.
        thms = scan_decls(root, BRIDGE_DIR, ("theorem",))
        twins = []
        for r in self.rows:
            for twin in [r.d] + r.arms:
                twins.append((twin, r))
        by_leaf = collections.defaultdict(list)
        for twin, r in twins:
            by_leaf[twin.leaf].append((twin, r))
        pool = collections.defaultdict(list)
        for twin, r in twins:
            pool[twin.leaf[:1]].append((twin, r))
        self.t1_ambiguous = []
        self.t1_doc = []
        for t in thms:
            cands = []
            for twin, r in pool.get(t.leaf[:1], ()):
                tag = t1_tag(t.leaf, twin.leaf)
                if tag is None:
                    continue
                rank = ns_rank(t.ns, twin.ns)
                if rank is None:
                    continue
                cands.append(((-len(twin.leaf), rank,
                               0 if tier_of_bridge(t.path) == r.tier else 1,
                               twin.path, twin.lineno), twin, r, tag))
            cands.sort(key=lambda c: c[0])
            if cands and t1_recognised(cands[0][3]):
                if len(cands) > 1 and cands[0][0][:2] == cands[1][0][:2] \
                        and cands[0][2] is not cands[1][2]:
                    self.t1_ambiguous.append(
                        (t, sorted({"%s@%s"
                                    % (c[2].d.full,
                                       c[2].d.path[len(ARENA_DIR) + 1:])
                                    for c in cands})))
                cands[0][2].t1.append((t, cands[0][3]))
                continue
            # The name says nothing this script recognises.  The ESCAPE HATCH:
            # `Theorem 1 for `X`` in the theorem's OWN doc block names its
            # subject outright, whatever the theorem is called.  It is only
            # consulted here, so a doc comment that names the twin a `_spec`
            # is the entry point OF (`instantiateListFast_spec`, "THEOREM 1
            # for `instantiateList`, at the entry point") does not move the
            # credit off the twin the theorem is literally about.
            doc = self.t1_doc_claim(t, by_leaf)
            if doc is not None:
                self.t1_doc.append((t, doc[0].full))
                doc[1].t1.append((t, "(doc)"))
            elif cands:
                cands[0][2].t1_other.append(t)

        # -- T2: the `Lean twin:` citations and the Refine2 lemmas
        self.wire_rust(root)
        refs = scan_decls(root, REFINE2_DIR, ("theorem",))
        # `<fn>_refines` first, then the store/spec tier's own shapes — the
        # ORDER matters, because a function may have both and `_refines` is
        # the one to name in the table.
        by_stem = {}
        for suf, nc in T2_SUFFIXES:
            for t in refs:
                if t.leaf.endswith(suf) and len(t.leaf) > len(suf):
                    by_stem.setdefault(t.leaf[:-len(suf)], (t, nc, suf))
        self.t2_shapes = collections.Counter()
        # The self-check's candidates are the Refine2 theorems that are NOT
        # already some OTHER Rust function's statement: without that cut,
        # `basis_pin_hit_go_refines` would be reported as "a theorem naming
        # `basis_pin_hit` under another shape", which it is not.
        def claimed(name):
            for suf, _ in T2_SUFFIXES:
                if name.endswith(suf) and name[:-len(suf)] in self.all_rust_fns:
                    return True
            return False

        ref_names = [t.leaf for t in refs if not claimed(t.leaf)]
        other = collections.defaultdict(list)
        for r in self.rows:
            for fn, _, _ in r.rust:
                # the bare `fn` name first, then the receiver-qualified one:
                # `Tbl.find?`'s Rust is `Tbl::find` and its lemma is
                # `tbl_find_abs`, not `find_abs`
                hit = by_stem.get(fn)
                for alias in (r.qual.get(fn) or ()):
                    if hit:
                        break
                    hit = by_stem.get(alias)
                r.t2[fn] = None if hit is None else (hit[0], hit[1])
                if hit is not None:
                    self.t2_shapes[hit[2]] += 1
                else:
                    if fn not in other:
                        other[fn] = [n for n in ref_names if mentions_fn(n, fn)]
                    r.t2_other += other[fn]

        for (path, decl), (scope, reason) in sorted(skips.items()):
            if decl == "*":
                continue
            r = self.by_key.get((path, decl)) \
                or next((x for x in self.rows
                         if x.d.path == path and x.d.name == decl), None)
            if r is None:
                continue
            if scope in ("T1", "BOTH") and r.t1_stated:
                self.skip_redundant.append((path, decl, "T1"))
            if scope in ("T2", "BOTH") and r.t2_stated:
                self.skip_redundant.append((path, decl, "T2"))

    def t1_doc_claim(self, t, by_leaf):
        """(twin, row) if Bridge theorem `t`'s OWN doc comment says
        "Theorem 1 for `X`" and `X` is a twin, else None.

        The convention's escape hatch, and the reason the self-check's
        "unrecognised suffix" list is a finding rather than a backlog: a
        statement whose name does not end in `_spec`/`_run`/… can still SAY
        that it is the statement, and `Bridge/ExprOps/Subst.lean`'s
        `eidxCopyUpto_toList` does exactly that.  A module or section header
        does not count — only the `/-- … -/` block attached to the theorem,
        which is what `Decl.a` starts at."""
        lines = file_lines(self.root, t.path)
        head = "\n".join(lines[t.a - 1:t.lineno])
        for m in T1_DOC_RE.finditer(head):
            named = strip_root(m.group(1))
            leaf = named.split(".")[-1]
            best = None
            for twin, r in by_leaf.get(leaf, ()):
                if ns_rank(tuple(named.split(".")[:-1]), twin.ns) is None:
                    continue
                key = (0 if tier_of_bridge(t.path) == r.tier else 1,
                       twin.path, twin.lineno)
                if best is None or key < best[0]:
                    best = (key, twin, r)
            if best is not None:
                return best[1], best[2]
        return None

    def wire_rust(self, root):
        """Every `Lean twin:` citation, attributed to the Rust item below it
        and to the twin (or the twin's dispatcher) it names."""
        save, T.REPO = T.REPO, root
        try:
            twins = T.collect(T.ROOTS)
        finally:
            T.REPO = save
        by_file = collections.defaultdict(list)
        for t in twins:
            by_file[t.file].append(t)
        # every twin of a file, arms included (an arm points at its
        # dispatcher's row), indexed by the module the citation names
        disp = collections.defaultdict(list)
        for r in self.rows:
            disp[r.d.path].append((r.d, r))
            for a in r.arms:
                disp[a.path].append((a, r))
        save, P.REPO = P.REPO, root
        try:
            for f in P.rust_files(list(T.ROOTS)):
                for i, q in with_impl(f, P.scan_rust_file(f)[0]):
                    if i.kind == "fn":
                        self.all_rust_fns.add(i.name())
                        self.all_rust_fns.update(q)
        finally:
            P.REPO = save
        for f, ts in sorted(by_file.items()):
            items, _, _ = P.scan_rust_file(f)
            items = sorted(items, key=lambda i: i.lineno)
            quals = dict((i.lineno, q) for i, q in with_impl(f, items))
            for t in sorted(ts, key=lambda t: t.lineno):
                if t.name is None:
                    continue
                row = self.row_for(t.path, t.name, disp, t.a)
                if row is None:
                    continue
                item = next((i for i in items if i.lineno >= t.lineno), None)
                if item is None or item.kind != "fn":
                    self.non_fn_citations += 1
                    continue
                ent = (item.name(), os.path.relpath(f, root), t.lineno)
                if ent[0] not in [e[0] for e in row.rust]:
                    row.rust.append(ent)
                    row.qual[ent[0]] = quals.get(item.lineno)

    def row_for(self, path, name, disp, cited_line=None):
        """The row a `Lean twin:` citation names.

        The NAME is the authority — `scripts/twin-lines.py update` relocates a
        citation by name and rewrites only the digits — so the qualified name
        decides first: `EStore.find?` is `EStore`'s, never `Tbl`'s, even when
        the citation's range has rotted onto `Tbl.find?`.  The cited RANGE is
        the tiebreak, and it is the one that settles the four `dropScratch` of
        `Arena/Store.lean`, which the unqualified citation cannot."""
        cands = []
        for d, row in disp.get(path, ()):
            full = P.names_compatible(d.full, name)
            if not (full or P.names_compatible(d.name, name)):
                continue
            inside = 0 if (cited_line is not None
                           and d.a <= cited_line <= d.b) else 1
            cands.append(((0 if full else 1, 0 if d.full == name else 1,
                           inside, d.lineno), row))
        if not cands:
            return None
        cands.sort(key=lambda c: c[0])
        return cands[0][1]


# ------------------------------------------------------------------ output

def counts(rows):
    c = collections.Counter()
    for r in rows:
        c["twins"] += 1
        c["arms"] += len(r.arms)
        if r.t1_skipped:
            c["t1_skip"] += 1
        else:
            c["t1_scope"] += 1
            c["t1_stated"] += bool(r.t1_stated)
            c["t1_closed"] += bool(r.t1_closed)
        if r.t2_skipped:
            c["t2_skip"] += 1
        else:
            c["t2_scope"] += 1
            c["t2_cited"] += bool(r.t2_cited)
            c["t2_stated"] += bool(r.t2_stated)
            c["t2_closed"] += bool(r.t2_closed)
    return c


def pct(a, b):
    return "%d%%" % (100 * a // b) if b else "-"


def tier_rows(census):
    groups = collections.defaultdict(list)
    for r in census.rows:
        groups[r.tier].append(r)
    order = sorted(groups, key=lambda t: (TIER_ORDER.index(t)
                                          if t in TIER_ORDER else 99, t))
    return [(t, groups[t]) for t in order]


def self_check(census):
    """The four self-check populations.

    `blind` is the honest "nothing anywhere names this twin"; `odd` is the
    dangerous one — a theorem DOES name it, under a suffix this script does
    not know, and without this line it would pass silently as "unstated"."""
    blind = [r for r in census.rows
             if not r.t1 and not r.t1_other and not r.t1_skipped]
    odd = [r for r in census.rows
           if not r.t1 and r.t1_other and not r.t1_skipped]
    t2_blind = [r for r in census.rows if r.t2_cited and not r.t2_stated
                and not r.t2_other and not r.t2_skipped]
    t2_odd = [r for r in census.rows
              if r.t2_cited and not r.t2_stated and r.t2_other]
    # Round 2 made one theorem credit one twin (`t1_candidates`), so this is
    # 0 by construction and the line stays as the assertion that it is.
    seen = collections.Counter()
    for r in census.rows:
        for t, _ in r.t1:
            seen[(t.path, t.name)] += 1
    shared = sum(1 for k, n in seen.items() if n > 1)
    return blind, odd, t2_blind, t2_odd, shared


def print_summary(census):
    print("%-17s %6s %10s %9s %10s %9s %9s"
          % ("tier", "twins", "T1 stated", "T1 closed", "T2 cited",
             "T2 stated", "T2 closed"))
    for tier, rows in tier_rows(census):
        c = counts(rows)
        print("%-17s %6d %10s %9s %10s %9s %9s"
              % ("Arena/" + tier, c["twins"],
                 "%d/%d" % (c["t1_stated"], c["t1_scope"]),
                 "%d" % c["t1_closed"],
                 "%d/%d" % (c["t2_cited"], c["t2_scope"]),
                 "%d" % c["t2_stated"], "%d" % c["t2_closed"]))
    c = counts(census.rows)
    print("%-17s %6d %10s %9s %10s %9s %9s"
          % ("TOTAL", c["twins"],
             "%d/%d" % (c["t1_stated"], c["t1_scope"]),
             "%d" % c["t1_closed"],
             "%d/%d" % (c["t2_cited"], c["t2_scope"]),
             "%d" % c["t2_stated"], "%d" % c["t2_closed"]))
    print("arena census: %d twins (+%d arms folded in, %d skipped for T1, "
          "%d for T2) | T1 stated %s closed %s | T2 stated %s closed %s"
          % (c["twins"], c["arms"], c["t1_skip"], c["t2_skip"],
             pct(c["t1_stated"], c["t1_scope"]),
             pct(c["t1_closed"], c["t1_scope"]),
             pct(c["t2_stated"], c["t2_scope"]),
             pct(c["t2_closed"], c["t2_scope"])))
    print_checkline(census)


def print_checkline(census):
    blind, odd, t2_blind, t2_odd, shared = self_check(census)
    extra = []
    if shared:
        extra.append("%d Bridge theorem(s) credited to more than one twin "
                     "(same leaf, two modules)" % shared)
    if census.orphan_arms:
        extra.append("%d `Arm` def(s) with no unique dispatcher"
                     % len(census.orphan_arms))
    if census.skip_bad:
        extra.append("%d MALFORMED skip line(s)" % len(census.skip_bad))
    if census.skip_stale:
        extra.append("%d STALE skip(s)" % len(census.skip_stale))
    if census.skip_redundant:
        extra.append("%d REDUNDANT skip(s)" % len(census.skip_redundant))
    if census.t1_ambiguous:
        extra.append("%d Bridge theorem(s) whose twin is AMBIGUOUS (credited "
                     "to the first, by module then line)"
                     % len(census.t1_ambiguous))
    print("self-check: %d twin(s) with NO Bridge theorem naming them at all; "
          "%d matched ONLY by an unrecognised suffix (a convention this "
          "script does not know)%s"
          % (len(blind), len(odd), ("; " + ", ".join(extra)) if extra else ""))
    if odd:
        names = sorted({r.t1_other[0].name for r in odd})
        print("  T1 unrecognised: " + ", ".join(names[:12])
              + (" …" if len(names) > 12 else ""))
    if census.t1_doc:
        print("  T1 by doc comment: %d theorem(s) over %d twin(s) say "
              "\"Theorem 1 for `X`\" — %s"
              % (len(census.t1_doc), len({n for _, n in census.t1_doc}),
                 ", ".join(sorted({"%s → %s" % (t.name, n)
                                   for t, n in census.t1_doc}))))
    for t, names in census.t1_ambiguous:
        print("  AMBIGUOUS %s:%d %s — %s"
              % (t.path[len(BRIDGE_DIR) + 1:], t.lineno, t.name,
                 " / ".join(names)))
    for a in census.orphan_arms:
        print("  ORPHAN ARM %s:%d %s"
              % (a.path[len(ARENA_DIR) + 1:], a.lineno, a.full))
    print("self-check (T2): %d cited twin(s) with NO Refine2 theorem naming "
          "their Rust function at all; %d named by a theorem under another "
          "shape (not one of %s)"
          % (len(t2_blind), len(t2_odd),
             "/".join(s for s, _ in T2_SUFFIXES)))
    if census.t2_shapes:
        print("  T2 shapes used: "
              + ", ".join("%s %d" % (s, census.t2_shapes[s])
                          for s, _ in T2_SUFFIXES if census.t2_shapes[s]))
    if t2_odd:
        names = sorted({r.t2_other[0] for r in t2_odd})
        print("  T2 other shape: " + ", ".join(names[:12])
              + (" …" if len(names) > 12 else ""))
    for ln, text in census.skip_bad:
        print("  MALFORMED %s:%d  %s" % (SKIP_FILE, ln, text))
    for path, decl, why in census.skip_stale:
        print("  STALE %s %s — %s" % (path, decl, why))
    for path, decl, which in census.skip_redundant:
        print("  REDUNDANT %s %s — %s is stated after all" % (path, decl, which))


def print_table(census):
    print("%-10s %-34s %-30s %-8s %-26s %-26s %-8s"
          % ("tier", "twin", "file:line", "T1", "T1 theorem", "T2 theorem",
             "T2"))
    for tier, rows in tier_rows(census):
        for r in sorted(rows, key=lambda r: (r.d.path, r.d.lineno)):
            s1, n1 = r.t1_cell()
            s2, n2 = r.t2_cell()
            print("%-10s %-34s %-30s %-8s %-26s %-26s %-8s"
                  % (tier, r.d.name[:34],
                     ("%s:%d" % (r.d.path[len(ARENA_DIR) + 1:], r.d.lineno))[:30],
                     s1, n1[:26], n2[:26], s2))
    print()
    print_summary(census)


def print_md(census):
    print("| tier | twins | T1 owed | T1 stated | T1 closed | T2 owed "
          "| T2 cited | T2 stated | T2 closed |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")

    def row(label, c, bold=False):
        b = "**" if bold else ""
        print("| %s%s%s | %s%d%s | %s%d%s | %s%d (%s)%s | %s%d (%s)%s | "
              "%s%d%s | %s%d (%s)%s | %s%d (%s)%s | %s%d (%s)%s |"
              % (b, label, b, b, c["twins"], b, b, c["t1_scope"], b,
                 b, c["t1_stated"], pct(c["t1_stated"], c["t1_scope"]), b,
                 b, c["t1_closed"], pct(c["t1_closed"], c["t1_scope"]), b,
                 b, c["t2_scope"], b,
                 b, c["t2_cited"], pct(c["t2_cited"], c["t2_scope"]), b,
                 b, c["t2_stated"], pct(c["t2_stated"], c["t2_scope"]), b,
                 b, c["t2_closed"], pct(c["t2_closed"], c["t2_scope"]), b))

    for tier, rows in tier_rows(census):
        row("`Arena/%s`" % tier, counts(rows))
    row("total", counts(census.rows), bold=True)


OPEN_GROUPS = (
    ("T1 UNSTATED — no Bridge theorem", lambda r: not r.t1_skipped and not r.t1),
    ("T1 SORRY — stated, not closed",
     lambda r: not r.t1_skipped and r.t1 and not r.t1_closed),
    ("T2 UNCITED — no Rust function names this twin",
     lambda r: not r.t2_skipped and not r.t2_cited),
    ("T2 UNSTATED — cited, but no `<fn>_refines`/`_abs`/`_run`/`_obs`",
     lambda r: not r.t2_skipped and r.t2_cited and not r.t2_stated),
    ("T2 SORRY — stated, not closed",
     lambda r: not r.t2_skipped and r.t2_stated and not r.t2_closed),
)


def print_open(census):
    for title, pred in OPEN_GROUPS:
        rows = [r for r in census.rows if pred(r)]
        print("== %s: %d" % (title, len(rows)))
        per = collections.Counter(r.tier for r in rows)
        if per:
            print("   " + "  ".join("%s %d" % (t, per[t])
                                    for t, _ in tier_rows(census) if per[t]))
        for r in sorted(rows, key=lambda r: (TIER_ORDER.index(r.tier)
                                             if r.tier in TIER_ORDER else 99,
                                             r.d.path, r.d.lineno)):
            extra = ""
            if title.startswith("T2 UNSTATED"):
                extra = "  [%s]" % ", ".join(
                    f for f, _, _ in r.rust if not r.t2.get(f))
            print("   %-34s %s%s"
                  % (r.d.name[:34],
                     "%s:%d" % (r.d.path[len(ARENA_DIR) + 1:], r.d.lineno),
                     extra))
        print()
    print_summary(census)


# --------------------------------------------------------------- self-test

def self_check_counts(census):
    """The self-check line as a dict, so `--selftest` can pin it too.

    A verdict table alone would not catch a regression in the parts of the
    census that are ABOUT the conventions rather than about one row — the
    doc-comment rule, the ambiguity report, which T2 shape was used.  These
    are the `@` lines of `expected.txt`."""
    blind, odd, t2_blind, t2_odd, shared = self_check(census)
    out = {
        "t1_blind": len(blind),
        "t1_other": len(odd),
        "t1_doc": len(census.t1_doc),
        "t1_ambiguous": len(census.t1_ambiguous),
        "t1_shared": shared,
        "t2_blind": len(t2_blind),
        "t2_other": len(t2_odd),
        "orphan_arms": len(census.orphan_arms),
        "skip_bad": len(census.skip_bad),
        "skip_stale": len(census.skip_stale),
        "skip_redundant": len(census.skip_redundant),
    }
    for suf, _ in T2_SUFFIXES:
        out["t2_shape" + suf] = census.t2_shapes[suf]
    return out


def cmd_selftest(verbose):
    """The census over `scripts/testdata/arena-census/`, a miniature of the
    real tree, against its committed verdicts."""
    if not os.path.isdir(FIXTURE):
        print("selftest: no fixture at %s" % FIXTURE)
        return 2
    census = Census(FIXTURE)
    got = {}
    for r in census.rows:
        s1, _ = r.t1_cell()
        s2, _ = r.t2_cell()
        got[r.d.full] = "%s %s" % (s1, s2)
    counts_got = self_check_counts(census)
    expected, counts_want = {}, {}
    with open(os.path.join(FIXTURE, "expected.txt"), encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("@"):
                _, key, val = line.split(None, 2)
                counts_want[key] = int(val.split()[0])
                continue
            name, t1, t2, _rest = (line.split(None, 3) + [""])[:4]
            expected[name] = "%s %s" % (t1, t2)
    bad = 0
    for name in sorted(set(expected) | set(got)):
        e, g = expected.get(name, "<absent>"), got.get(name, "<absent>")
        if e != g:
            print("MISMATCH %-30s expected %-16s got %s" % (name, e, g))
            bad += 1
        elif verbose:
            print("ok       %-30s %s" % (name, g))
    for key in sorted(set(counts_want) | set(counts_got)):
        e = counts_want.get(key)
        g = counts_got.get(key)
        if e is None or e != g:
            print("MISMATCH @%-29s expected %-16s got %s"
                  % (key, "<absent>" if e is None else e,
                     "<absent>" if g is None else g))
            bad += 1
        elif verbose:
            print("ok       @%-29s %s" % (key, g))
    if bad:
        print("selftest: %d mismatch(es) of %d row(s) and %d self-check "
              "count(s)." % (bad, len(expected), len(counts_got)))
        return 1
    print("selftest: %d fixture row(s) and %d self-check count(s), every "
          "verdict as recorded." % (len(got), len(counts_got)))
    return 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--md", action="store_true")
    ap.add_argument("--open", action="store_true", dest="open_")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return cmd_selftest(args.verbose)
    census = Census(REPO)
    if args.summary:
        print_summary(census)
    elif args.md:
        print_md(census)
        print()
        print_checkline(census)
    elif args.open_:
        print_open(census)
    else:
        print_table(census)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

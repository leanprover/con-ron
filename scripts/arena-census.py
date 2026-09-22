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
`proof/ConRon/Arena/**`, mutual-block members included (they sit at column 0
and `provenance.top_level_decls` already sees them).  NOT `theorem`s (the
arena's own verification is not a thing the bridge restates), NOT
`structure` / `inductive` / `class` / `instance` (a type is mirrored by the
denotation, not by a theorem about a function), and NOT `abbrev` — the
arena's 33 are type synonyms (`abbrev EIdx := Idx .expr`, `abbrev AM :=
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

Every OTHER `X…` theorem name — `_ext`, `_pext`, `_step`, `_of_not_lam`,
`_leaf`, … — is a side lemma, not the statement, and does NOT count as
"stated".  But it is not thrown away either: a twin whose only match is an
unrecognised suffix is counted and listed in the self-check line, so a
convention this script does not know cannot pass silently as "unstated".

--------------------------------------------------- the T2 conventions

The `Lean twin:` line is the arrow from the Rust to the twin, and
`scripts/twin-lines.py`'s parser is what reads it (one parser, one set of
rules — the same argument that file makes about `provenance.py`).  A
citation sits in the doc block of the Rust item just below it; the item's
`fn` name is the T2 subject.  `proof/ConRon/Refine2/**` then states

    <rust_fn>_refines     the refinement lemma (761 of them at the tip), or
    <rust_fn>_no_claim    the "this arm claims nothing" lemma (15), which
                          counts as stated AND closed, flagged `N` in the
                          table — a `Native` decline or an error constructor
                          the port deliberately does not model.

A twin cited by several Rust functions (a store projection is cited from
four call sites) needs one `_refines` EACH: the row is `T2 stated` only when
every citing function has one, and `--open` names the ones that do not.

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
                a twenty-row miniature of the real tree, and compare with
                the committed verdicts

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

ARM_RE = re.compile(r"Arm[A-Z]")
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


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
    """One top-level declaration, with its block and whether it is proved."""

    def __init__(self, path, lineno, kw, name, a, b, has_sorry):
        self.path = path
        self.lineno = lineno
        self.kw = kw
        self.name = name
        self.a = a
        self.b = b
        self.has_sorry = has_sorry


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


def scan_decls(root, sub, kws):
    """Every top-level declaration of `<root>/<sub>/**` whose keyword is in
    `kws`, as `Decl`s, in file then line order."""
    out = []
    for path in lean_files(root, sub):
        lines = file_lines(root, path)
        skip = P.comment_lines(lines)
        for lineno, kw, name in P.top_level_decls(lines):
            if kw not in kws:
                continue
            a, b = P.extend_block(lines, lineno - 1)
            out.append(Decl(path, lineno, kw, name, a, b,
                            block_has_sorry(lines, skip, a, b)))
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

def t1_match(thm_name, twin_name):
    """Does Bridge theorem `thm_name` state something about twin `twin_name`?

    Returns the recognised suffix, or None — which is not the same as "about
    nothing": the caller has already attributed the theorem to this twin by
    longest-prefix, so a None here means an UNRECOGNISED suffix and the row
    goes to `t1_other`, which the self-check line reports."""
    for suf in T1_SUFFIXES:
        if thm_name.endswith(suf) and names_eq(thm_name[:-len(suf)], twin_name):
            return suf
    for suf in T1_PREFIX_SUFFIXES:
        i = thm_name.rfind(suf)
        while i > 0:
            if names_eq(thm_name[:i], twin_name):
                return thm_name[i:]
            i = thm_name.rfind(suf, 0, i)
    return None


def names_eq(stem, twin):
    """`provenance.names_compatible`, narrowed: a citation may drop or add a
    NAMESPACE, but never name a namespace and match inside it."""
    if not stem:
        return False
    return (stem == twin or twin.endswith("." + stem)
            or stem.endswith("." + twin))


def longest_leaf(thm_leaf, leaves):
    """The LONGEST twin leaf `thm_leaf` starts with, or None.

    Longest wins because the short names are prefixes of the long ones:
    `EIdx_hasLevelParam_spec` is `hasLevelParam`'s statement, not a side
    lemma of the twin `EIdx`, and attributing it by the first match found
    would put it in the wrong row (and inflate the self-check's
    "unrecognised suffix" count with it)."""
    best = None
    for leaf in leaves:
        if thm_leaf == leaf or thm_leaf.startswith(leaf + "_") \
                or thm_leaf.startswith(leaf + "'"):
            if best is None or len(leaf) > len(best):
                best = leaf
    return best


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
            arms = [d for d in ds if ARM_RE.search(d.name)]
            if not arms:
                continue
            lines = file_lines(root, path)
            others = [d for d in ds if not ARM_RE.search(d.name)]
            bodies = [(o, "\n".join(lines[o.a - 1:o.b])) for o in others]
            for arm in arms:
                pat = re.compile(r"(?<![A-Za-z0-9_'.])"
                                 + re.escape(arm.name.split(".")[-1])
                                 + r"(?![A-Za-z0-9_'])")
                hits = [o for o, body in bodies if pat.search(body)]
                if len(hits) == 1:
                    owner[(path, arm.name)] = hits[0].name
                else:
                    self.orphan_arms.append(arm)

        rows = {}
        for d in defs:
            if (d.path, d.name) in owner:
                continue
            rows[(d.path, d.name)] = Row(d, tier_of(d.path))
        for d in defs:
            key = owner.get((d.path, d.name))
            if key is not None and (d.path, key) in rows:
                rows[(d.path, key)].arms.append(d)
        self.rows = list(rows.values())
        self.by_key = rows

        # -- the skips
        skips, self.skip_bad = load_skips(root)
        names = collections.defaultdict(set)
        for d in defs:
            names[d.path].add(d.name)
        for (path, decl), (scope, reason) in sorted(skips.items()):
            if path not in names:
                self.skip_stale.append((path, decl, "no such arena module"))
            elif decl != "*" and decl not in names[path]:
                self.skip_stale.append((path, decl, "no such definition"))
        for r in self.rows:
            s = skip_for(skips, r.d.path, r.d.name)
            if s:
                r.skip = s

        # -- T1: the Bridge theorems
        thms = scan_decls(root, BRIDGE_DIR, ("theorem",))
        # Every twin leaf (arms included), longest first: a theorem is
        # attributed to the LONGEST twin name it starts with, so
        # `EIdx_hasLevelParam_spec` is `hasLevelParam`'s and not `EIdx`'s.
        leaves = set()
        for r in self.rows:
            for twin in [r.d] + r.arms:
                leaves.add(twin.name.split(".")[-1])
        cand = collections.defaultdict(list)
        for t in thms:
            leaf = longest_leaf(t.name.split(".")[-1], leaves)
            if leaf is not None:
                cand[leaf].append(t)
        for r in self.rows:
            for twin in [r.d] + r.arms:
                leaf = twin.name.split(".")[-1]
                for t in cand.get(leaf, ()):
                    suf = t1_match(t.name, twin.name) \
                        or t1_match(t.name.split(".")[-1], twin.name)
                    if suf:
                        r.t1.append((t, suf))
                    else:
                        r.t1_other.append(t)

        # -- T2: the `Lean twin:` citations and the Refine2 lemmas
        self.wire_rust(root)
        refs = scan_decls(root, REFINE2_DIR, ("theorem",))
        by_stem = {}
        for t in refs:
            for suf, nc in (("_refines", False), ("_no_claim", True)):
                if t.name.endswith(suf):
                    by_stem.setdefault(t.name[:-len(suf)], (t, nc))
        # The self-check's candidates are the Refine2 theorems that are NOT
        # already some OTHER Rust function's `_refines`: without that cut,
        # `basis_pin_hit_go_refines` would be reported as "a theorem naming
        # `basis_pin_hit` under another shape", which it is not.
        def claimed(name):
            for suf in ("_refines", "_no_claim"):
                if name.endswith(suf) and name[:-len(suf)] in self.all_rust_fns:
                    return True
            return False

        ref_names = [t.name for t in refs if not claimed(t.name)]
        other = collections.defaultdict(list)
        for r in self.rows:
            for fn, _, _ in r.rust:
                r.t2[fn] = by_stem.get(fn)
                if r.t2[fn] is None:
                    if fn not in other:
                        other[fn] = [n for n in ref_names if mentions_fn(n, fn)]
                    r.t2_other += other[fn]

        for (path, decl), (scope, reason) in sorted(skips.items()):
            if decl == "*":
                continue
            r = self.by_key.get((path, decl))
            if r is None:
                continue
            if scope in ("T1", "BOTH") and r.t1_stated:
                self.skip_redundant.append((path, decl, "T1"))
            if scope in ("T2", "BOTH") and r.t2_stated:
                self.skip_redundant.append((path, decl, "T2"))

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
        # the twin's dispatcher, for an arm the Rust cites after all
        disp = {}
        for r in self.rows:
            for a in r.arms:
                disp[(a.path, a.name)] = r
        save, P.REPO = P.REPO, root
        try:
            for f in P.rust_files(list(T.ROOTS)):
                for i in P.scan_rust_file(f)[0]:
                    if i.kind == "fn":
                        self.all_rust_fns.add(i.name())
        finally:
            P.REPO = save
        for f, ts in sorted(by_file.items()):
            items, _, _ = P.scan_rust_file(f)
            items = sorted(items, key=lambda i: i.lineno)
            for t in sorted(ts, key=lambda t: t.lineno):
                if t.name is None:
                    continue
                row = self.row_for(t.path, t.name, disp)
                if row is None:
                    continue
                item = next((i for i in items if i.lineno >= t.lineno), None)
                if item is None or item.kind != "fn":
                    self.non_fn_citations += 1
                    continue
                ent = (item.name(), os.path.relpath(f, root), t.lineno)
                if ent[0] not in [e[0] for e in row.rust]:
                    row.rust.append(ent)

    def row_for(self, path, name, disp):
        r = self.by_key.get((path, name))
        if r is not None:
            return r
        r = disp.get((path, name))
        if r is not None:
            return r
        # the citation may drop or add a namespace
        leaf = name.split(".")[-1]
        for (p, n), row in self.by_key.items():
            if p == path and (n == name or n.split(".")[-1] == leaf):
                return row
        for (p, n), row in disp.items():
            if p == path and (n == name or n.split(".")[-1] == leaf):
                return row
        return None


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
    # One unqualified theorem, two twins with the same leaf in two modules
    # (`viewApp` is `Monad.lean`'s wrapper AND `Store.lean`'s projection):
    # the theorem is credited to both, and the row says "stated" for both.
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
    print("self-check: %d twin(s) with NO Bridge theorem naming them at all; "
          "%d matched ONLY by an unrecognised suffix (a convention this "
          "script does not know)%s"
          % (len(blind), len(odd), ("; " + ", ".join(extra)) if extra else ""))
    if odd:
        names = sorted({r.t1_other[0].name for r in odd})
        print("  T1 unrecognised: " + ", ".join(names[:12])
              + (" …" if len(names) > 12 else ""))
    print("self-check (T2): %d cited twin(s) with NO Refine2 theorem naming "
          "their Rust function at all; %d named by a theorem under another "
          "shape (the store tier's `_abs`/`_run` specs, not `_refines`)"
          % (len(t2_blind), len(t2_odd)))
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
    ("T2 UNSTATED — cited, but no `<fn>_refines`",
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

def cmd_selftest(verbose):
    """The census over `scripts/testdata/arena-census/`, a twenty-row
    miniature of the real tree, against its committed verdicts."""
    if not os.path.isdir(FIXTURE):
        print("selftest: no fixture at %s" % FIXTURE)
        return 2
    census = Census(FIXTURE)
    got = {}
    for r in census.rows:
        s1, _ = r.t1_cell()
        s2, _ = r.t2_cell()
        got[r.d.name] = "%s %s" % (s1, s2)
    expected = {}
    with open(os.path.join(FIXTURE, "expected.txt"), encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
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
    if bad:
        print("selftest: %d mismatch(es) of %d row(s)." % (bad, len(expected)))
        return 1
    print("selftest: %d fixture row(s), every verdict as recorded." % len(got))
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

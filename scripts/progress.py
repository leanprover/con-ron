#!/usr/bin/env python3
"""scripts/progress.py — the quantitative progress report (DESIGN.md §7).

Three numbers per con-leche implementation file, in *Lean lines*:

  to translate   lines inside definitional top-level blocks (`def`, `abbrev`,
                 `inductive`, `structure`, `class`, `instance`, `opaque` — not
                 `theorem`s), MINUS the blocks of the declarations
                 `scripts/provenance-skip.txt` lists as deliberately not
                 ported, each with its reason (task #33);
  translated     of those, the blocks of the declarations some Rust item
                 cites (`/// con-leche: path:A-B decl`, scripts/provenance.py
                 `coverage`'s own predicate: a citation whose range contains
                 the declaration's line, or whose name is the declaration's);
  verified       of those, the blocks of the declarations cited by a Rust item
                 `f` in module `m` for which `proof/ConRon/Refine/<M>.lean`
                 states `theorem f_refines` (the §3.5 exact-result lemma);
  skipped        the blocks of the deliberate skips, reported separately.

The unit of the ledger is a *declaration* (as in `coverage`); the line counts
weight it by the size of its block, doc comment included.  So a citation that
names a declaration credits the whole declaration, which is what makes the two
reports agree.

Three groups since task #84: the verified core (`ConLeche/Kernel`,
`ConLeche/Cached`); the **parser in the core** (`ConLeche/Frontend`'s
recogniser, record assembly, projection rewrite, ground hoist, preparation and
prelude — verified-core Rust whose `_refines` lemmas task #85 writes, so its
`verified` column is 0 by construction until then); and the cherries that stay
unverified (the in-process modeller, the annotated-NDJSON writer and its debug
splice, `Main.lean`).  `Frontend/Scan/Equiv` — the parser's own equivalence
proofs — is excluded throughout: it is a `Prop`, not code.  Plus the size of
the Rust, the generated Lean and the proofs.

Usage: scripts/progress.py [--md | --summary] [--shape OLD_RE NEW_RE]
`--summary` prints only the totals (what scripts/gates.sh shows).  The
lemma-shape line counts statements in the old vs the new convention of a
running campaign (default: accept-direction vs full-outcome, task #67); the
stale count lists lemmas whose Rust item carries a provenance CHANGED marker
(a con-leche bump that moved or changed the cited code, before anyone
rebuilds).  A lemma that still builds against the regenerated model is
current by construction; the gates are the oracle for code drift.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import provenance as P  # noqa: E402

REPO = P.REPO
CORE_GLOBS = ["ConLeche/Kernel", "ConLeche/Cached"]
# The parser moved into `crates/con-ron-core` at task #84, so it is no longer
# a cherry: it is verified-core Rust with no `_refines` lemma *yet* (task #85
# writes those).  It gets its own row rather than joining `CORE_GLOBS`,
# because merging it would silently drop the checker's own verified
# percentage by diluting it with a tier nobody has proved.  `Scan/Naive.lean`
# belongs here and not with the modeller: it is the recogniser's
# *specification*, and `scan_fast` cites its declarations where a `Fast`
# function is the `@[csimp]` twin of a `Naive` one.
PARSER_GLOBS = [
    "ConLeche/Frontend/Scan/Types.lean",
    "ConLeche/Frontend/Scan/Fast.lean",
    "ConLeche/Frontend/Scan/Naive.lean",
    "ConLeche/Frontend/Export.lean",
    "ConLeche/Frontend/ExportC.lean",
    "ConLeche/Frontend/ProjRec.lean",
    "ConLeche/Frontend/NatOpGround.lean",
    "ConLeche/Frontend/Prepare.lean",
    "ConLeche/Frontend/Prelude.lean",
]
# What is left unverified: the in-process modeller (task #84's ruling — its
# correctness decides coverage, not soundness), the annotated-NDJSON writer
# and its debug splice, and the driver.
CHERRY_GLOBS = [
    "ConLeche/Frontend/InModel",
    "ConLeche/Frontend/InModel.lean",
    "ConLeche/Frontend/ExportWrite.lean",
    "ConLeche/Frontend/InModelDump.lean",
    "Main.lean",
]
CHERRY_EXCLUDE = re.compile(r"ConLeche/Frontend/Scan/Equiv")
# What is not to be ported is no longer a regex here: it is
# `scripts/provenance-skip.txt`, one `path decl reason` line per declaration
# (task #33).  The four wholly-skipped files — `BasisGen`, `CoreGated`,
# `CheckerGated`, `CoreIO` — are `*` entries in it, so they show up in the
# table with 0 to translate and their declarations counted as skipped.
# The citation roots the ledger reads.  `crates/con-ron/src` joined at task
# #37 so the *cherries* table starts counting: it is the unverified frontend,
# so nothing in it will ever have a `_refines` lemma, and the "verified"
# column of the cherries rows stays 0 by construction.  The `Rust core` size
# line below still counts `CORE_RUST_ROOT` alone.
RUST_ROOTS = ["crates/con-ron-core/src", "crates/con-ron/src"]
CORE_RUST_ROOT = "crates/con-ron-core/src"
REFINE_DIR = "proof/ConRon/Refine"
GENERATED_DIR = "proof/ConRon/Generated"


def lean_files(globs):
    out = []
    for sub in globs:
        base = os.path.join(REPO, P.CON_LECHE, sub)
        if os.path.isfile(base):
            out.append(sub)
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(dirnames)
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = os.path.join(dirpath, fn)
                    out.append(os.path.relpath(full, os.path.join(REPO, P.CON_LECHE)))
    return sorted(set(out))


def definitional_blocks(lines):
    """[(name, lineno, set of 1-based lines)] per definitional top-level block."""
    got = []
    for lineno, kw, name in P.top_level_decls(lines):
        if kw not in P.DEFINITIONAL:
            continue
        a, b = P.extend_block(lines, lineno - 1)
        got.append((name, lineno, set(range(a, b + 1))))
    return got


def covered_by(name, lineno, cites):
    """`coverage`'s predicate: does any of `cites` claim this declaration?"""
    return any(c.a <= lineno <= c.b or P.names_compatible(name, c.decl)
               for c in cites)


# Statement-shape classification (campaigns).  A lemma's statement is the
# text from `theorem` to `:= by`/`:=`/`where`; ACCEPT matches the accept-
# direction convention of §3.5 (a hypothesis `= ok (.Ok …`), FULL the
# full-outcome convention of the 2026-09-13 ruling (an `.Err` clause, or one
# of the restated `Refines*` definitions).  Override with `--shape OLD NEW`.
SHAPE_OLD = r"= ok \(\.Ok |core\.result\.Result\.Ok"
SHAPE_NEW = r"\.Err\b|core\.result\.Result\.Err"
LEMMA_SHAPES = {}  # (module, fn) -> "full" | "accept" | "na" | "other"
SHAPE_DEFS = {}    # name of a statement-packaging `def`/`structure` -> its shape
SHAPE_BODIES = {}  # the same definitions' bodies, for the resolution pass below


def shape_defs(old_re, new_re):
    """Shared statement shapes (`RefinesE`, `Sim`, `KnotSpec`, …): every
    `def`/`structure`/`abbrev` under Refine/ whose body says what a Rust
    `Result` means (`= ok` on the Rust side, `= .ok` on con-leche's); each
    gets the shape of its own body, so a lemma stated through it inherits it
    even though the lemma's text never changes when the def is restated."""
    d = os.path.join(REPO, REFINE_DIR)
    for dirpath, _dirs, files in os.walk(d):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            text = open(os.path.join(dirpath, fn), encoding="utf-8").read()
            for m in re.finditer(r"^(?:def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_.]*)\b(.*?)(?=^(?:def|abbrev|structure|theorem|lemma|end|namespace|section|/--|/-!)\b)", text, re.M | re.S):
                body = m.group(2)
                # A statement-packaging definition is one that says what a Rust
                # `Result` means.  It may spell the Rust side `= ok` (`Sim`,
                # `RefinesE`) or the con-leche side `= .ok` (`Out`, `OutP`,
                # whose Rust outcome is a bare `match` argument); both are
                # shapes a lemma can be stated through, and the campaign found
                # that missing the second silently moved a restated lemma out
                # of scope instead of counting it (task #67 continued).
                if not re.search(r"=\s*\.?ok\b|Result\.ok\b", body):
                    continue
                name = m.group(1).split(".")[-1]
                SHAPE_DEFS[name] = classify_text(body, old_re, new_re)
                SHAPE_BODIES[name] = body
    # One packaging definition is often written through another: `Sim`/`SimS`
    # say their outcome obligation is `State.Out`, and read on their own they
    # classify as neither convention.  Resolve to a fixpoint so a lemma stated
    # through the outer one inherits the inner one's shape.
    for _ in range(4):
        changed = False
        for name, shape in list(SHAPE_DEFS.items()):
            if shape in ("full", "accept"):
                continue
            for other, oshape in SHAPE_DEFS.items():
                if other == name or oshape not in ("full", "accept"):
                    continue
                if re.search(r"\b%s\b" % re.escape(other), SHAPE_BODIES[name]):
                    SHAPE_DEFS[name] = oshape
                    changed = True
                    break
        if not changed:
            break


def classify_text(stmt, old_re, new_re):
    if re.search(new_re, stmt):
        return "full"
    if re.search(old_re, stmt):
        return "accept"
    if re.search(SHAPE_NA, stmt) and not re.search(r"\.Ok\b", stmt):
        return "na"
    return "other"


SHAPE_NA = r"= ok [a-zA-Z_(\[]"  # a `Result T` with no `CheckError` inside: no error arm to restate


def classify(stmt, old_re, new_re):
    """full: restated in the new convention; accept: still in the old one;
    n/a: the function cannot return a `CheckError` (a plain `= ok r`), so the
    campaign does not touch it; other: unclassified.  A statement written
    through a shared shape definition inherits that definition's shape."""
    direct = classify_text(stmt, old_re, new_re)
    if direct in ("full", "accept"):
        return direct
    # Several packaging names can occur in one statement — `IndAbs.checkFuelU`
    # sits in the hypothesis list of every lemma of the inductive tier, beside
    # the `State.Out` that carries the shape.  Returning whichever one the file
    # walk happened to reach first made a restated lemma read as out of scope
    # (task #67 continued), so a shape that classifies the campaign wins over
    # one that does not.
    shapes = {shape for name, shape in SHAPE_DEFS.items()
              if re.search(r"\b%s\b" % re.escape(name), stmt)}
    for pref in ("full", "accept"):
        if pref in shapes:
            return pref
    return direct


OPENERS = "([{⟨⦃"
CLOSERS = ")]}⟩⦄"


def statement_end(text, start):
    """Where a `theorem`'s statement ends: the `:=` (or `where`) that
    introduces its *proof*, which is the first one at bracket depth 0.

    A plain `(.*?)(?::=|\\bwhere\\b)` capture stops at the first `:=`
    anywhere, and Lean's named-argument syntax puts one *inside* the
    statement — `ConLeche.liftFueled (m := ConLeche.CheckM) …`.  The campaign
    found that truncating there hides a full-outcome statement's `.Err` arm
    and reports the lemma as unclassified (task #67 continued).  Strings are
    skipped so a bracket inside a message does not unbalance the scan.
    """
    i, n, depth = start, len(text), 0
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                return i
            if (text.startswith("where", i)
                    and not (text[i - 1].isalnum() or text[i - 1] == "_")
                    and (i + 5 >= n or not (text[i + 5].isalnum()
                                            or text[i + 5] == "_"))):
                return i
        i += 1
    return n


def refine_lemmas(old_re=SHAPE_OLD, new_re=SHAPE_NEW):
    """{(ModuleLower, fn)} for every `theorem <fn>_refines` under Refine/,
    recursively; a file in a subdirectory `Refine/Core/Arms/X.lean` counts
    for the module `corec` (the knot lives in `cached/core_c.rs`).  Also
    fills LEMMA_SHAPES with each lemma's statement shape."""
    if not SHAPE_DEFS:
        shape_defs(old_re, new_re)
    out = set()
    d = os.path.join(REPO, REFINE_DIR)
    if not os.path.isdir(d):
        return out
    for dirpath, _dirs, files in os.walk(d):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            rel = os.path.relpath(dirpath, d)
            if rel == ".":
                module = fn[:-5].lower().replace("_", "")
            elif rel.split(os.sep)[0] == "Core":
                module = "corec"
            else:
                module = rel.split(os.sep)[0].lower() + fn[:-5].lower().replace("_", "")
            text = open(os.path.join(dirpath, fn), encoding="utf-8").read()
            for m in re.finditer(r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_]*)_refines\b", text, re.M):
                key = (module, m.group(1))
                out.add(key)
                stmt = text[m.end():statement_end(text, m.end())]
                LEMMA_SHAPES[key] = classify(stmt, old_re, new_re)
    return out


def lemma_for(lemmas, module, fn):
    """A lemma `fn_refines` counts for Rust module `m` if it sits in
    `Refine/<M>.lean` or in a themed sibling `Refine/<M><Suffix>.lean`
    (`ExprOpsSpine.lean` for `expr_ops`), or in a directory file
    `Refine/<M>/<File>.lean` (not scanned here; keep names flat)."""
    for lm, lf in lemmas:
        if lf == fn and lm.startswith(module):
            return True
    return False


def rust_module_of(item):
    """The Rust module name a lemma file is matched against.  Modules in a
    subdirectory carry the directory as a prefix (`inductives/struct_parts.rs`
    → `indstructparts`, matching `Refine/IndStructParts.lean`; `core_c.rs`
    under `cached/` stays `corec`, its lemmas live in `Refine/Core/*`)."""
    base = os.path.basename(item.file)
    name = base[:-3].lower().replace("_", "") if base.endswith(".rs") else base
    parent = os.path.basename(os.path.dirname(item.file))
    if parent == "inductives":
        return "ind" + name
    return name


def count_lines(paths):
    n = 0
    for p in paths:
        try:
            with open(p, encoding="utf-8") as f:
                n += sum(1 for _ in f)
        except OSError:
            pass
    return n


def walk(root, ext):
    out = []
    for dirpath, _d, files in os.walk(os.path.join(REPO, root)):
        for fn in files:
            if fn.endswith(ext):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def main(argv):
    md = "--md" in argv
    summary = "--summary" in argv
    old_re, new_re = SHAPE_OLD, SHAPE_NEW
    if "--shape" in argv:
        i = argv.index("--shape")
        old_re, new_re = argv[i + 1], argv[i + 2]
    items, cites, _malformed, markers = P.collect([os.path.join(REPO, r) for r in RUST_ROOTS])
    lemmas = refine_lemmas(old_re, new_re)
    # Stale lemmas: the Rust item carries a provenance CHANGED marker (a
    # con-leche bump moved or changed its source; scripts/provenance.py update).
    marked = set()
    for mk in markers:  # (path, lineno, body) from provenance.scan_rust_file
        f, ln = mk[0], mk[1]
        for it in sorted((i for i in items if i.file == f), key=lambda i: i.lineno):
            if it.lineno >= ln:
                marked.add((rust_module_of(it), it.name()))
                break
    stale = sorted(k for k in lemmas if k in marked)

    # Citations per con-leche file, and the subset that belongs to a Rust item
    # with its `_refines` lemma.
    cited = {}    # path -> [Cite]
    proved = {}   # path -> [Cite]
    for it in items:
        has_lemma = lemma_for(lemmas, rust_module_of(it), it.name())
        for c in it.cites:
            if c is None:
                continue
            cited.setdefault(c.path, []).append(c)
            if has_lemma:
                proved.setdefault(c.path, []).append(c)

    skips, bad = P.load_skips()
    for lineno, line in bad:
        print("MALFORMED %s:%d — a skip needs `<path> <decl> <reason>`: %s"
              % (P.SKIP_FILE, lineno, line), file=sys.stderr)

    def report(title, globs, exclude=None):
        rows = []
        tot = [0, 0, 0, 0, 0]
        for path in lean_files(globs):
            if exclude and exclude.search(path):
                continue
            full = os.path.join(REPO, P.CON_LECHE, path)
            lines = open(full, encoding="utf-8").read().split("\n")
            cs, ps = cited.get(path, []), proved.get(path, [])
            d = t = v = sk = 0
            for name, lineno, blk in definitional_blocks(lines):
                if (path, name) in skips or (path, "*") in skips:
                    sk += len(blk)
                    continue
                d += len(blk)
                if covered_by(name, lineno, cs):
                    t += len(blk)
                if covered_by(name, lineno, ps):
                    v += len(blk)
            rows.append((path, len(lines), d, t, v, sk))
            tot[0] += len(lines); tot[1] += d; tot[2] += t; tot[3] += v; tot[4] += sk
        rows.sort(key=lambda r: -r[2])
        pct = lambda a, b: ("%3d%%" % (100 * a // b)) if b else "  -"
        if summary:
            print("%-58s to translate %6d  translated %6d (%s)  verified %6d (%s)  skipped %5d"
                  % (title, tot[1], tot[2], pct(tot[2], tot[1]).strip(), tot[3],
                     pct(tot[3], tot[1]).strip(), tot[4]))
        elif md:
            print("### %s\n" % title)
            print("| file | raw | to translate | translated | verified | skipped |")
            print("|---|---:|---:|---:|---:|---:|")
            for p, raw, d, t, v, sk in rows:
                if d == 0 and sk == 0:
                    continue
                print("| `%s` | %d | %d | %d (%s) | %d (%s) | %d |"
                      % (p, raw, d, t, pct(t, d), v, pct(v, d), sk))
            print("| **total** | %d | **%d** | **%d (%s)** | **%d (%s)** | **%d** |\n"
                  % (tot[0], tot[1], tot[2], pct(tot[2], tot[1]), tot[3],
                     pct(tot[3], tot[1]), tot[4]))
        else:
            print("== %s" % title)
            print("%-52s %6s %8s %14s %14s %8s"
                  % ("file", "raw", "to-xlat", "translated", "verified", "skipped"))
            for p, raw, d, t, v, sk in rows:
                if d == 0 and sk == 0:
                    continue
                print("%-52s %6d %8d %8d %s %8d %s %8d"
                      % (p, raw, d, t, pct(t, d), v, pct(v, d), sk))
            print("%-52s %6d %8d %8d %s %8d %s %8d\n"
                  % ("TOTAL", tot[0], tot[1], tot[2], pct(tot[2], tot[1]), tot[3],
                     pct(tot[3], tot[1]), tot[4]))
        return tot

    core = report("Verified core (ConLeche/Kernel, ConLeche/Cached)", CORE_GLOBS)
    parser = report("Parser in the core (ConLeche/Frontend, task #84)", PARSER_GLOBS)
    cherry = report("Cherries (InModel, ExportWrite, Main.lean)", CHERRY_GLOBS, CHERRY_EXCLUDE)

    rust = count_lines(walk(CORE_RUST_ROOT, ".rs"))
    rust_unverified = count_lines(walk("crates", ".rs")) - rust
    gen = count_lines(walk(GENERATED_DIR, ".lean"))
    proofs = count_lines(walk(REFINE_DIR, ".lean"))
    core_dir = os.path.join(REPO, CORE_RUST_ROOT)
    n_items = sum(1 for it in items
                  if it.kind == "fn" and it.file.startswith(core_dir))
    n_lemmas = len(lemmas)
    pin = (P.current_submodule_commit() or "?")[:8]
    shapes = {"full": 0, "accept": 0, "na": 0, "other": 0}
    for k in lemmas:
        shapes[LEMMA_SHAPES.get(k, "other")] += 1
    if summary:
        print("Rust core %d lines (%d fns) | unverified crates %d | generated Lean %d | proofs %d (%d _refines) | pin %s"
              % (rust, n_items, rust_unverified, gen, proofs, n_lemmas, pin))
        camp = shapes["full"] + shapes["accept"]
        print("Campaign (task #67): full-outcome %d / %d in scope (%d%%), accept-direction left %d; no error arm %d, unclassified %d | stale (CHANGED marker) %d"
              % (shapes["full"], camp, 100 * shapes["full"] // max(camp, 1), shapes["accept"], shapes["na"], shapes["other"], len(stale)))
        if stale:
            print("  stale: " + ", ".join("%s.%s" % k for k in stale[:20]) + (" …" if len(stale) > 20 else ""))
    elif md:
        print("### Sizes\n")
        print("| what | lines |\n|---|---:|")
        print("| Rust, verified core (`crates/con-ron-core`) | %d |" % rust)
        print("| Rust, unverified crates | %d |" % rust_unverified)
        print("| generated Lean (`%s`) | %d |" % (GENERATED_DIR, gen))
        print("| refinement proofs (`%s`) | %d |" % (REFINE_DIR, proofs))
        print("| Rust functions / `_refines` lemmas | %d / %d |" % (n_items, n_lemmas))
        print("| campaign: full-outcome / accept-direction left / no error arm / unclassified | %d / %d / %d / %d |" % (shapes["full"], shapes["accept"], shapes["na"], shapes["other"]))
        print("| stale lemmas (provenance CHANGED marker on the Rust item) | %d |" % len(stale))
        print("\ncon-leche pin `%s`.  Core: %d%% translated, %d%% verified." % (
            pin, 100 * core[2] // max(core[1], 1), 100 * core[3] // max(core[1], 1)))
    else:
        print("Rust verified core %d lines; unverified crates %d; generated Lean %d; proofs %d; Rust fns %d, _refines lemmas %d; pin %s"
              % (rust, rust_unverified, gen, proofs, n_items, n_lemmas, pin))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

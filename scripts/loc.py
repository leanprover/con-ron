#!/usr/bin/env python3
"""scripts/loc.py — the four sizes side by side (DESIGN.md §7).

For every Rust module of the verified core, in lines:

  upstream   the con-leche lines its items cite: the definitional blocks of
             the declarations claimed by the module's `/// con-leche:`
             citations (the `progress.py` ledger's unit, doc comment
             included; a declaration cited from two modules counts for both
             rows and once in the total);
  rust       the module's lines outside `#[cfg(test)]`/`mod tests`;
  generated  the lines of the Aeneas model (`proof/ConRon/Generated/*`)
             whose `Source:` marker names the module;
  proof      the lines of the `proof/ConRon/Refine/` files that belong to the
             module by the naming convention of `progress.py` (`Refine/Level*.lean`
             ↔ `kernel/level.rs`, `Refine/Core/*` ↔ `cached/core_c.rs`,
             `Refine/IndFoo*.lean` ↔ `kernel/inductives/foo.rs`), split by
             how each theorem is proved:
               tactic   a `by` block without `grind` (the hand proofs),
               grind    a proof that calls `grind`/`rust_grind` (the task
                        #70/#71 idiom, task #71's ruling: new proofs only),
               term     a term-mode proof (`:= foo …`),
               other    everything that is not a theorem: the abstraction
                        functions, relations, `Spec`s, docs, imports.

Refine files that match no module (`Abs`, `State`, `Main`, `IndSpec`, …) are the shared infrastructure, reported as one row;
`Refine/Automation/*` is the study, reported separately and kept out of the
proof total.  Ratios at the bottom.

`kernel/pins_text.rs` (the embedded pins text) is data: shown, not totalled.

`--by-upstream` turns the table around: one row per core con-leche file, the
Rust/generated/proof lines attributed *per item* — a Rust item's span from
the model's `Source:` marker, its generated chunk, and the theorems named
`<fn>_refines*`; helper lemmas and infrastructure are not attributable that
way and are reported as one "not attributed" line.  `--md` for Markdown,
`--summary` for the totals line.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import provenance as P  # noqa: E402
import progress as PR  # noqa: E402

REPO = P.REPO
CORE_RUST_ROOT = "crates/con-ron-core/src"
REFINE_DIR = "proof/ConRon/Refine"
GENERATED_DIR = "proof/ConRon/Generated"
GRIND_RE = re.compile(r"\b(?:rust_grind|grind)\b")
# Rust files that are data, not code: kept as rows, left out of the totals.
DATA_FILES = {"kernel/pins_text.rs"}  # the embedded `con-ron-pins/1` text (task #43)
# Refine files whose name does not start with their Rust module's key.
ALIASES = {"indc": "indinductivesc"}


# ------------------------------------------------------------------ Rust

def rust_nontest_lines(path):
    """Lines outside `#[cfg(test)]` blocks and `mod tests`."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    n = 0
    depth = 0
    test_depth = None
    pending = False
    for raw in lines:
        code = P.strip_code(raw)
        if test_depth is None and (P.CFG_TEST_RE.match(raw) or P.MOD_TESTS_RE.match(raw)):
            pending = True
        counted = test_depth is None and not pending
        before = depth
        depth += code.count("{") - code.count("}")
        if pending and depth > before:
            test_depth = before
            pending = False
        elif pending and ";" in code:
            pending = False
        if counted:
            n += 1
        if test_depth is not None and depth <= test_depth:
            test_depth = None
    while lines and lines[-1].strip() == "":
        lines.pop()
        n -= 1
    return max(n, 0)


def mod_key(rust_file):
    """`progress.rust_module_of` on a path."""
    class _I:
        pass
    it = _I()
    it.file = rust_file
    return PR.rust_module_of(it)


def rust_modules():
    files = PR.walk(CORE_RUST_ROOT, ".rs")
    return [(os.path.relpath(f, os.path.join(REPO, CORE_RUST_ROOT)), f) for f in files]


# ------------------------------------------------------------------ generated

SOURCE_RE = re.compile(r"Source: '([^']*)', lines (\d+):\d+-(\d+):\d+")


def generated_chunks():
    """[(rust_rel_file | None, a, b, nlines, name)] one per `/-- [name]:` block
    of the model; `None` for the Rust standard library's."""
    out = []
    for f in PR.walk(GENERATED_DIR, ".lean"):
        lines = open(f, encoding="utf-8").read().split("\n")
        starts = [i for i, l in enumerate(lines) if l.startswith("/-- [")]
        for k, i in enumerate(starts):
            j = starts[k + 1] if k + 1 < len(starts) else len(lines)
            while j > i and lines[j - 1].strip() == "":
                j -= 1
            chunk = "\n".join(lines[i:min(i + 4, j)])
            m = SOURCE_RE.search(chunk)
            name = lines[i][5:].split("]")[0]
            if not m or not m.group(1).startswith("crates/"):
                out.append((None, 0, 0, j - i, name))
                continue
            out.append((m.group(1), int(m.group(2)), int(m.group(3)), j - i, name))
    return out


# ------------------------------------------------------------------ proofs

def refine_files():
    """[(rel path, module key or 'shared' or 'study')]"""
    d = os.path.join(REPO, REFINE_DIR)
    keys = set(mod_key(f) for _r, f in rust_modules())
    out = []
    for dirpath, _dirs, files in os.walk(d):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            rel = os.path.relpath(dirpath, d)
            if rel == ".":
                fk = fn[:-5].lower().replace("_", "")
            elif rel.split(os.sep)[0] == "Core":
                fk = "corec"
            elif rel.split(os.sep)[0] == "Automation":
                fk = None
            else:
                fk = rel.split(os.sep)[0].lower() + fn[:-5].lower().replace("_", "")
            if fk is None:
                mod = "study"
            elif fk in ALIASES:
                mod = ALIASES[fk]
            elif fk.startswith("pins"):
                mod = "pinsdecode"  # `Refine/Pins*.lean` are the decoder's proofs (task #43)
            else:
                cands = [k for k in keys if fk.startswith(k)]
                mod = max(cands, key=len) if cands else "shared"
            out.append((os.path.relpath(os.path.join(dirpath, fn), REPO), mod))
    return out


def classify_proofs(path):
    """{'tactic','grind','term','other'} -> lines, plus theorem counts and
    the list of (name, class, lines) for the `_refines` attribution."""
    lines = open(os.path.join(REPO, path), encoding="utf-8").read().split("\n")
    while lines and lines[-1].strip() == "":
        lines.pop()
    total = len(lines)
    res = {"tactic": 0, "grind": 0, "term": 0, "other": 0}
    cnt = {"tactic": 0, "grind": 0, "term": 0}
    thms = []
    covered = 0
    for lineno, kw, name in P.top_level_decls(lines):
        if kw not in ("theorem", "lemma"):
            continue
        a, b = P.extend_block(lines, lineno - 1)
        body = "\n".join(lines[lineno - 1:b])
        if GRIND_RE.search(body):
            c = "grind"
        elif re.search(r":=\s*by\b|^\s*by\b", body, re.M):
            c = "tactic"
        else:
            c = "term"
        n = b - a + 1
        res[c] += n
        cnt[c] += 1
        covered += n
        thms.append((name, c, n))
    res["other"] = max(total - covered, 0)
    return res, cnt, thms, total


# ------------------------------------------------------------------ upstream

def ledger():
    """{path: [(name, lineno, blocklen)]} for the core and the cherries, skips
    removed."""
    skips, _bad = P.load_skips()
    out = {}
    for globs in (PR.CORE_GLOBS, PR.CHERRY_GLOBS):
        for path in PR.lean_files(globs):
            if PR.CHERRY_EXCLUDE.search(path):
                continue
            lines = open(os.path.join(REPO, P.CON_LECHE, path), encoding="utf-8").read().split("\n")
            decls = []
            for name, lineno, blk in PR.definitional_blocks(lines):
                if (path, name) in skips or (path, "*") in skips:
                    continue
                decls.append((name, lineno, len(blk)))
            out[path] = decls
    return out


def cited_decls(item, led):
    got = set()
    for c in item.cites:
        if c is None or not isinstance(c, P.Cite):
            continue
        for name, lineno, n in led.get(c.path, []):
            if c.a <= lineno <= c.b or P.names_compatible(name, c.decl):
                got.add((c.path, name, n))
    return got


# ------------------------------------------------------------------ report

def fmt_ratio(a, b):
    return "%.2f" % (a / b) if b else "  -"


def by_rust(md, summary):
    items, _cites, _mal, _markers = P.collect([os.path.join(REPO, CORE_RUST_ROOT)])
    led = ledger()
    chunks = generated_chunks()
    gen_by_file = {}
    gen_external = 0
    for rf, _a, _b, n, _name in chunks:
        if rf is None:
            gen_external += n
        else:
            gen_by_file[rf] = gen_by_file.get(rf, 0) + n
    rows = []
    up_all = set()
    tot = {"up": 0, "rust": 0, "gen": 0, "proof": 0,
           "tactic": 0, "grind": 0, "term": 0, "other": 0,
           "n_tactic": 0, "n_grind": 0, "n_term": 0}
    proofs_by_mod = {}
    for path, mod in refine_files():
        res, cnt, _thms, total = classify_proofs(path)
        acc = proofs_by_mod.setdefault(mod, {"total": 0, "tactic": 0, "grind": 0, "term": 0, "other": 0,
                                             "n_tactic": 0, "n_grind": 0, "n_term": 0, "files": 0})
        acc["total"] += total
        acc["files"] += 1
        for k in ("tactic", "grind", "term", "other"):
            acc[k] += res[k]
        for k in ("tactic", "grind", "term"):
            acc["n_" + k] += cnt[k]
    for rel, full in rust_modules():
        key = mod_key(full)
        up = set()
        for it in items:
            if it.file == full:
                up |= cited_decls(it, led)
        up_all |= up
        upn = sum(n for _p, _n, n in up)
        rust = rust_nontest_lines(full)
        gen = gen_by_file.get(os.path.join(CORE_RUST_ROOT, rel), 0)
        pr = proofs_by_mod.get(key, {"total": 0, "tactic": 0, "grind": 0, "term": 0, "other": 0,
                                     "n_tactic": 0, "n_grind": 0, "n_term": 0, "files": 0})
        rows.append((rel, upn, rust, gen, pr))
        if rel in DATA_FILES:
            continue
        tot["rust"] += rust
        tot["gen"] += gen
        tot["proof"] += pr["total"]
        for k in ("tactic", "grind", "term", "other", "n_tactic", "n_grind", "n_term"):
            tot[k] += pr[k]
    tot["up"] = sum(n for _p, _n, n in up_all)
    shared = proofs_by_mod.get("shared")
    study = proofs_by_mod.get("study")
    if shared:
        tot["proof"] += shared["total"]
        for k in ("tactic", "grind", "term", "other", "n_tactic", "n_grind", "n_term"):
            tot[k] += shared[k]
    rows.sort(key=lambda r: -r[2])

    def pr_cell(pr):
        return "%d/%d/%d/%d" % (pr["tactic"], pr["grind"], pr["term"], pr["other"])

    def pr_n(pr):
        return "%d/%d/%d" % (pr["n_tactic"], pr["n_grind"], pr["n_term"])

    if summary:
        print("LoC: upstream %d | rust %d | generated %d | proof %d (tactic %d in %d thms, grind %d in %d, term %d in %d, other %d) | study %d | ratios rust/up %s gen/rust %s proof/rust %s proof/up %s"
              % (tot["up"], tot["rust"], tot["gen"], tot["proof"],
                 tot["tactic"], tot["n_tactic"], tot["grind"], tot["n_grind"],
                 tot["term"], tot["n_term"], tot["other"],
                 study["total"] if study else 0,
                 fmt_ratio(tot["rust"], tot["up"]), fmt_ratio(tot["gen"], tot["rust"]),
                 fmt_ratio(tot["proof"], tot["rust"]), fmt_ratio(tot["proof"], tot["up"])))
        return
    if md:
        print("| Rust module | upstream | rust | generated | proof | proof lines tactic/grind/term/other | theorems tactic/grind/term |")
        print("|---|---:|---:|---:|---:|---:|---:|")
        for rel, upn, rust, gen, pr in rows:
            tag = " (data, not in the total)" if rel in DATA_FILES else ""
            print("| `%s`%s | %d | %d | %d | %d | %s | %s |" % (rel, tag, upn, rust, gen, pr["total"], pr_cell(pr), pr_n(pr)))
        if shared:
            print("| *shared proof infrastructure (%d files)* | | | | %d | %s | %s |" % (shared["files"], shared["total"], pr_cell(shared), pr_n(shared)))
        print("| **total** | **%d** | **%d** | **%d** | **%d** | %s | %s |" % (tot["up"], tot["rust"], tot["gen"], tot["proof"], pr_cell(tot), pr_n(tot)))
        if study:
            print("| *study (`Refine/Automation`, not in the total)* | | | | %d | %s | %s |" % (study["total"], pr_cell(study), pr_n(study)))
        print("\nRatios: rust/upstream %s, generated/rust %s, proof/rust %s, proof/upstream %s; generated lines for the Rust standard library %d."
              % (fmt_ratio(tot["rust"], tot["up"]), fmt_ratio(tot["gen"], tot["rust"]),
                 fmt_ratio(tot["proof"], tot["rust"]), fmt_ratio(tot["proof"], tot["up"]), gen_external))
        return
    print("%-36s %8s %7s %9s %7s  %-24s %-12s" % ("Rust module", "upstream", "rust", "generated", "proof", "tactic/grind/term/other", "thms t/g/t"))
    for rel, upn, rust, gen, pr in rows:
        tag = " (data)" if rel in DATA_FILES else ""
        print("%-36s %8d %7d %9d %7d  %-24s %-12s" % (rel + tag, upn, rust, gen, pr["total"], pr_cell(pr), pr_n(pr)))
    if shared:
        print("%-36s %8s %7s %9s %7d  %-24s %-12s" % ("(shared infrastructure, %d files)" % shared["files"], "", "", "", shared["total"], pr_cell(shared), pr_n(shared)))
    print("%-36s %8d %7d %9d %7d  %-24s %-12s" % ("TOTAL", tot["up"], tot["rust"], tot["gen"], tot["proof"], pr_cell(tot), pr_n(tot)))
    if study:
        print("%-36s %8s %7s %9s %7d  %-24s %-12s" % ("(study, not in the total)", "", "", "", study["total"], pr_cell(study), pr_n(study)))
    print("\nratios: rust/upstream %s   generated/rust %s   proof/rust %s   proof/upstream %s   (generated lines for the Rust std: %d)"
          % (fmt_ratio(tot["rust"], tot["up"]), fmt_ratio(tot["gen"], tot["rust"]),
             fmt_ratio(tot["proof"], tot["rust"]), fmt_ratio(tot["proof"], tot["up"]), gen_external))


def by_upstream(md):
    items, _cites, _mal, _markers = P.collect([os.path.join(REPO, CORE_RUST_ROOT)])
    led = ledger()
    chunks = generated_chunks()
    # item -> (rust span, generated lines) via the model's Source markers
    spans = {}
    for rf, a, b, n, _name in chunks:
        if rf is None:
            continue
        spans.setdefault(os.path.join(REPO, rf), []).append((a, b, n))
    item_size = {}
    for it in items:
        best = None
        for a, b, n in spans.get(it.file, []):
            if a <= it.lineno <= b and (best is None or b - a < best[1] - best[0]):
                best = (a, b, n)
        item_size[id(it)] = (best[1] - best[0] + 1, best[2]) if best else (0, 0)
    # theorem blocks named <fn>_refines*
    thm_lines = {}
    proof_total = 0
    for path, mod in refine_files():
        if mod == "study":
            continue
        _res, _cnt, thms, total = classify_proofs(path)
        proof_total += total
        for name, _c, n in thms:
            m = re.match(r"([A-Za-z_][A-Za-z0-9_]*?)_refines", name.split(".")[-1])
            if m:
                thm_lines.setdefault(m.group(1), 0)
                thm_lines[m.group(1)] += n
    rows = []
    tot = [0, 0, 0, 0]
    attributed_proof = 0
    seen_items = set()
    seen_fns = set()
    core = set(PR.lean_files(PR.CORE_GLOBS))
    for path in sorted(led):
        if path not in core:
            continue  # the cherries: no verified Rust cites them
        decls = led[path]
        up = sum(n for _n, _l, n in decls)
        if up == 0:
            continue
        its = [it for it in items if any(isinstance(c, P.Cite) and c.path == path for c in it.cites)]
        rust = sum(item_size[id(it)][0] for it in its)
        gen = sum(item_size[id(it)][1] for it in its)
        fns = set(it.name() for it in its if it.kind == "fn")
        proof = sum(thm_lines.get(f, 0) for f in fns)
        rows.append((path, up, rust, gen, proof))
        tot[0] += up
        for it in its:
            if id(it) not in seen_items:
                seen_items.add(id(it))
                tot[1] += item_size[id(it)][0]
                tot[2] += item_size[id(it)][1]
        for f in fns:
            if f not in seen_fns:
                seen_fns.add(f)
                attributed_proof += thm_lines.get(f, 0)
    tot[3] = attributed_proof
    rows.sort(key=lambda r: -r[1])
    if md:
        print("| con-leche file | upstream | rust | generated | proof (`_refines` blocks) |")
        print("|---|---:|---:|---:|---:|")
        for p, up, rust, gen, proof in rows:
            print("| `%s` | %d | %d | %d | %d |" % (p, up, rust, gen, proof))
        print("| **total (each item once)** | **%d** | **%d** | **%d** | **%d** |" % tuple(tot))
        print("\nProof lines not attributable to one item (helpers, relations, infrastructure): %d of %d." % (proof_total - attributed_proof, proof_total))
        return
    print("%-52s %8s %7s %9s %7s" % ("con-leche file", "upstream", "rust", "generated", "proof"))
    for p, up, rust, gen, proof in rows:
        print("%-52s %8d %7d %9d %7d" % (p, up, rust, gen, proof))
    print("%-52s %8d %7d %9d %7d" % ("TOTAL (each item once)", *tot))
    print("\nproof lines not attributable to one item (helpers, relations, infrastructure): %d of %d"
          % (proof_total - attributed_proof, proof_total))


def main(argv):
    md = "--md" in argv
    if "--by-upstream" in argv:
        by_upstream(md)
    else:
        by_rust(md, "--summary" in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

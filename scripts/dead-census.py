#!/usr/bin/env python3
"""scripts/dead-census.py — the unused-declaration census of `proof/` (task #105).

Adapted from con-leche's `scripts/dead-census.py` (its task #221, with the
owner fold of its lane GATEFIX).  `scripts/dead-census.lean` dumps the
constant dependency graph of an imported environment; this driver runs it
over every BUILT module of `proof/ConRon/**`, chooses the seeds, walks the
graph, and folds what is left into source-level OWNERS.

    scripts/dead-census.py [--out DIR] [--skip-lean] [--check]

(`DEAD_CENSUS_ROOT=<another checkout>` runs it over that checkout's build.)

Run it after a full `lake build` in `proof/` (the passes import oleans; a
module with no `.olean` is reported, not imported).  Heavy: one pass imports
Mathlib, Aeneas, con-leche and every module of ours (~10 GB, a few minutes).

## LIVE = the union of

* the **capstone roots** (CAPSTONES below): the binary's two headline
  theorems and their `_embedded` forms, which compose Theorem 2, Theorem 1
  and con-leche — everything the project exists to prove is in their
  closure;
* every declaration of a **Test** module (a module whose last component
  contains `Test`), of the **tooling** (`ConRon.Tools.*`, the sorry
  frontier) and of the **extraction output** (`ConRon.Generated.*`: Aeneas
  translates the whole crate, so an unreached generated function is a Rust
  question — `scripts/dead-rust.py` — not a proof one);
* the executables' closures: `main` in each executable root (EXE_ROOTS: the
  arena driver, its bench, the table generator, the pin dump), each in a
  pass of its own because every one of them declares `main`;
* every declaration the README or OVERVIEW links by name;
* every `@[csimp]` theorem and, through the dump's extra edges, the
  `@[implemented_by]` targets;
* every **registered** declaration (`syntax`, `macro`, `elab`, `notation`,
  `instance`, `macro_rules`, `@[command_elab]`, …): invoked by
  registration, never by name.

## WHAT THE CENSUS CANNOT SEE

1. *syntactic-only uses*: a `simp`/`rw` argument the tactic did not end up
   needing leaves no trace in the proof term, so it reads dead — the build
   is the arbiter when such a declaration is cut;
2. a declaration used only by a tactic *at elaboration* (a `@[lockstep]`
   lemma the tactic tried and discarded) — likewise dead, and rightly so.

## DEAD = DELETABLE TOGETHER

Every constant is folded into its OWNER — the longest prefix of its
(de-privatised) name that is a source declaration of its own module
(equation lemmas, matchers, projections and constructors are not written
in the source).  An owner is dead when none of its constants is live.  The
DELETION SET is the fixpoint of the dead owners under two rules: an owner
used by an owner outside the set is held back, and a `@[simp]` owner is held
back unless its whole module goes.

## OUTPUT (default `_tmp/deadcode-<checkout key>/`)

    census.tsv     name / module / kind / live
    deletable.txt  the deletion set: owner / module / constants folded in
    users.tsv      each owner of the set with the owners that use it
    held.txt       dead owners held back, with the reason
    deletable-modules.txt  modules every owner of which is in the set
    unbuilt.txt    modules of proof/ConRon with no .olean (no target builds them)
    summary.txt    the counts, overall and per tier

`--check` exits 1 when the deletion set or `unbuilt.txt` is non-empty after
`scripts/dead-census-allow.txt` (owner or module names, one per line, with
the reason after a tab) — the gate form.
"""

import argparse
import hashlib
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT = os.environ.get("DEAD_CENSUS_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.dirname(os.path.abspath(__file__))
PROOF = os.path.join(ROOT, "proof")
ALLOW = os.path.join(SCRIPTS, "dead-census-allow.txt")

MODIFIERS = (r"(?:public\s+|private\s+|protected\s+|partial\s+|noncomputable\s+|meta\s+"
             r"|unsafe\s+|scoped\s+|local\s+|nonrec\s+)*")
DECL_RE = re.compile(
    r"^\s*" + MODIFIERS +
    r"(theorem|def|abbrev|instance|structure|inductive|class|opaque|axiom|lemma)"
    r"\s+([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")
REGISTERED_RE = re.compile(
    r"^\s*" + MODIFIERS +
    r"(?:syntax|macro|elab|notation|instance|macro_rules|declare_syntax_cat)\b"
    r"(?:\s*\(name\s*:=\s*([A-Za-z_][A-Za-z0-9_'!?.]*)\))?")
ELAB_MODULE_RE = re.compile(
    r"^@\[command_elab\b|^elab\s+\"[^\"]*\"[^\n]*:\s*command\b", re.M)
ATTR_RE = re.compile(r"^\s*@\[([^\]]*)\]")

SEED_ATTRS = {"command_elab", "term_elab", "tactic", "builtin_command_elab",
              "builtin_term_elab", "macro", "app_unexpander", "delab",
              "instance", "extern", "export", "init", "builtin_init",
              "implemented_by"}

CAPSTONES = [
    "ConRon.Capstone.model_exists",
    "ConRon.Capstone.no_False_declaration",
    "ConRon.Capstone.model_exists_embedded",
    "ConRon.Capstone.no_False_declaration_embedded",
]
# executable roots: each declares `main`, so each is a pass of its own
EXE_ROOTS = ["ConRon.Arena.Exe", "ConRon.Arena.Bench", "ConRon.Gen.Main",
             "ConRon.Dump.Pins"]
SEED_MODULE_PREFIXES = ("ConRon.Tools", "ConRon.Generated")
LINK_RE = re.compile(r"\[[^\]`]*`([A-Za-z_][A-Za-z0-9_'!?.]*)`[^\]]*\]"
                     r"\((?:https://[^)]*?/blob/[^/]+/)?(proof/ConRon/[^#)]+)\.lean")


def is_test_module(mod):
    return "Test" in mod.split(".")[-1]


def tier(mod):
    parts = mod.split(".")
    return ".".join(parts[:2]) if len(parts) > 1 else mod


def all_modules():
    mods = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(PROOF, "ConRon")):
        dirnames.sort()
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), PROOF)
                mods.append(rel[:-5].replace("/", "."))
    return ["ConRon"] + mods


def built(mod):
    return os.path.exists(os.path.join(PROOF, ".lake", "build", "lib", "lean",
                                       mod.replace(".", "/") + ".olean"))


def run_lean(mods, out_path):
    cmd = ["lake", "env", "lean", "--run", os.path.join(SCRIPTS, "dead-census.lean")] + mods
    with open(out_path, "w") as fh:
        r = subprocess.run(cmd, cwd=PROOF, stdout=fh, stderr=subprocess.PIPE)
    if r.returncode != 0:
        sys.stderr.write(r.stderr.decode()[-4000:])
        sys.exit(1)


def read_pass(path):
    graph, info, csimp = {}, {}, set()
    with open(path) as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if parts[0] == "#csimp":
                csimp.add(parts[1])
                continue
            if len(parts) < 4:
                continue
            name, mod, kind, deps = parts[:4]
            graph[name] = deps.split() if deps else []
            info[name] = (mod, kind)
    return graph, info, csimp


def module_file(mod):
    return "proof/" + mod.replace(".", "/") + ".lean"


def suffixes(name):
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


def source_index():
    decls = defaultdict(set)
    attrs = defaultdict(set)
    registered = defaultdict(set)
    elab_files = set()
    for dirpath, dirnames, filenames in os.walk(os.path.join(PROOF, "ConRon")):
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            path = os.path.relpath(os.path.join(dirpath, fn), ROOT)
            text = open(os.path.join(ROOT, path), errors="replace").read()
            if ELAB_MODULE_RE.search(text):
                elab_files.add(path)
            pending = set()
            for line in text.splitlines():
                a = ATTR_RE.match(line)
                if a:
                    for piece in a.group(1).split(","):
                        pending.add(piece.strip().split()[0] if piece.strip() else "")
                    line = line[a.end():]
                    if not line.strip():
                        continue
                    line = " " + line
                m = DECL_RE.match(line)
                if m:
                    decls[m.group(2)].add(path)
                    if pending:
                        attrs[(m.group(2), path)] |= pending
                    pending = set()
                    continue
                r = REGISTERED_RE.match(line)
                if r:
                    if r.group(1):
                        registered[r.group(1)].add(path)
                    pending = set()
                    continue
                if line.strip() and not line.lstrip().startswith("--"):
                    pending = set()
    return decls, attrs, registered, elab_files


def link_seeds():
    out = set()
    for doc in ("README.md", "OVERVIEW.md", "DESIGN.md"):
        try:
            text = open(os.path.join(ROOT, doc), errors="replace").read()
        except OSError:
            continue
        for n, path in LINK_RE.findall(text):
            out.add((n, path[len("proof/"):].replace("/", ".")))
    return out


def load_allow():
    allow = set()
    try:
        for line in open(ALLOW):
            line = line.split("#", 1)[0].rstrip("\n")
            if line.strip():
                allow.add(line.split("\t")[0].strip())
    except OSError:
        pass
    return allow


def main():
    key = hashlib.sha256(ROOT.encode()).hexdigest()[:12]
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=f"_tmp/deadcode-{key}")
    ap.add_argument("--skip-lean", action="store_true",
                    help="reuse the raw passes already in --out")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if anything outside the allowlist is deletable or unbuilt")
    args = ap.parse_args()
    out = os.path.join(ROOT, args.out)
    os.makedirs(out, exist_ok=True)

    mods = all_modules()
    unbuilt = [m for m in mods if not built(m)]
    have = [m for m in mods if built(m)]
    main_mods = [m for m in have if m not in EXE_ROOTS]
    exe_mods = [m for m in have if m in EXE_ROOTS]
    passes = [("main", main_mods)] + [(m, [m]) for m in exe_mods]
    if not args.skip_lean:
        for tag, ms in passes:
            run_lean(ms, os.path.join(out, f"pass-{tag}.tsv"))

    graph, info, csimp = {}, {}, set()
    exe_mains = set()
    for tag, _ms in passes:
        g2, i2, c2 = read_pass(os.path.join(out, f"pass-{tag}.tsv"))
        for n, ds in g2.items():
            if n in graph:
                graph[n] = sorted(set(graph[n]) | set(ds))
            else:
                graph[n], info[n] = ds, i2[n]
        csimp |= c2
        if tag != "main":
            exe_mains |= {n for n, (mod, _k) in i2.items() if mod == tag}

    decls, attrs, registered, elab_files = source_index()

    missing = [n for n in CAPSTONES if n not in graph]
    if missing:
        sys.stderr.write("dead-census: capstone names that no longer exist: "
                         + " ".join(missing) + "\n")
        sys.exit(1)
    seeds = set(CAPSTONES) | csimp | exe_mains
    for short, mod in sorted(link_seeds()):
        seeds |= {n for n, (m, _k) in info.items()
                  if m == mod and (n == short or n.endswith("." + short))}
    for n, (mod, _kind) in info.items():
        own = module_file(mod)
        if mod.startswith(SEED_MODULE_PREFIXES) or is_test_module(mod) or own in elab_files:
            seeds.add(n)
            continue
        for s in suffixes(n):
            if own in registered.get(s, ()) or attrs.get((s, own), set()) & SEED_ATTRS:
                seeds.add(n)
                break
            if s in decls:
                break
    seeds &= set(graph)
    for n in list(graph):
        if n.endswith("._unsafe_rec"):
            parent = n[: -len("._unsafe_rec")]
            if parent in graph:
                graph[parent] = sorted(set(graph[parent]) | {n})

    live, todo = set(), list(seeds)
    while todo:
        n = todo.pop()
        if n in live:
            continue
        live.add(n)
        todo.extend(graph.get(n, ()))

    with open(os.path.join(out, "census.tsv"), "w") as fh:
        for name in sorted(info):
            mod, kind = info[name]
            fh.write(f"{name}\t{mod}\t{kind}\t{1 if name in live else 0}\n")

    def has_source(name):
        mod = info[name][0]
        u = name
        pp = "_private." + mod + ".0."
        if u.startswith(pp):
            u = u[len(pp):]
        own = module_file(mod)
        return any(own in decls.get(x, ()) for x in suffixes(u))

    def owner(name, depth=0):
        if has_source(name):
            return name
        pp = "_private." + info[name][0] + ".0."
        u = name[len(pp):] if name.startswith(pp) else name
        parts = u.split(".")
        for k in range(len(parts) - 1, 0, -1):
            pre = ".".join(parts[:k])
            for c in (pp + pre, pre):
                if c in info and depth < 8:
                    return owner(c, depth + 1)
        return None

    own_of = {n: owner(n) for n in info}
    members = defaultdict(set)
    for n, o in own_of.items():
        members[o or n].add(n)
    owner_mod = {o: info[next(iter(ns))][0] for o, ns in members.items()}

    def is_matcher(n):
        return any(c.startswith(("match_", "_sparseCasesOn"))
                   for c in n.split(".")[1:])

    live_owner = {o for o, ns in members.items()
                  if ((o in live) if (o in info and has_source(o)) else (ns & live))}
    users = defaultdict(set)
    for n, ds in graph.items():
        on = own_of.get(n) or n
        for d in ds:
            od = own_of.get(d) or d
            if od != on and not is_matcher(d):
                users[od].add(on)

    def is_simp(o):
        own = module_file(owner_mod[o])
        return any("simp" in attrs.get((x, own), ()) for x in suffixes(o))

    held = {}
    sourced = {o for o in members if o in info and has_source(o)}
    S = {o for o in sourced if o not in live_owner}
    mod_owners = defaultdict(set)
    for o in members:
        mod_owners[owner_mod[o]].add(o)
    while True:
        changed = False
        for o in sorted(S):
            out_users = sorted(u for u in users[o] if u not in S)
            if out_users:
                S.discard(o); held[o] = "used by " + " ".join(out_users[:3]); changed = True
            elif is_simp(o) and not mod_owners[owner_mod[o]] <= S:
                S.discard(o); held[o] = "@[simp], module survives"; changed = True
        if not changed:
            break
    with open(os.path.join(out, "users.tsv"), "w") as fh:
        for o in sorted(S):
            fh.write(f"{o}\t{' '.join(sorted(users[o]))}\n")
    with open(os.path.join(out, "deletable.txt"), "w") as fh:
        for o in sorted(S, key=lambda o: (owner_mod[o], o)):
            fh.write(f"{o}\t{owner_mod[o]}\t{len(members[o])}\n")
    with open(os.path.join(out, "held.txt"), "w") as fh:
        for o in sorted(held):
            fh.write(f"{o}\t{owner_mod.get(o, '?')}\t{held[o]}\n")
    whole = sorted(m for m, os_ in mod_owners.items() if os_ <= S)
    with open(os.path.join(out, "deletable-modules.txt"), "w") as fh:
        for m in whole:
            fh.write(m + "\n")
    with open(os.path.join(out, "unbuilt.txt"), "w") as fh:
        for m in unbuilt:
            fh.write(m + "\n")

    dead_by_tier = defaultdict(int)
    all_by_tier = defaultdict(int)
    for o in sourced:
        all_by_tier[tier(owner_mod[o])] += 1
        if o not in live_owner:
            dead_by_tier[tier(owner_mod[o])] += 1
    lines = [
        f"constants (ours):  {len(info)}",
        f"live:              {len(live)}",
        f"source owners:     {len(sourced)} ({len(sourced & live_owner)} live, "
        f"{len(sourced - live_owner)} dead)",
        f"deletion set:      {len(S)} owners, {sum(len(members[o]) for o in S)} constants"
        f" ({len(held)} held back); {len(whole)} modules whole",
        f"unbuilt modules:   {len(unbuilt)}",
        "dead source owners by tier:",
    ]
    for t in sorted(all_by_tier):
        lines.append(f"  {t:<24} {dead_by_tier[t]:>6} / {all_by_tier[t]}")
    summary = "\n".join(lines) + "\n"
    with open(os.path.join(out, "summary.txt"), "w") as fh:
        fh.write(summary)
    sys.stdout.write(summary)
    if args.check:
        allow = load_allow()
        bad = [o for o in S if o not in allow and owner_mod[o] not in allow]
        badm = [m for m in unbuilt if m not in allow]
        for o in sorted(bad)[:50]:
            sys.stdout.write(f"DEAD {o} ({owner_mod[o]})\n")
        for m in badm:
            sys.stdout.write(f"UNBUILT {m}\n")
        if bad or badm:
            sys.stdout.write(f"dead-census: {len(bad)} deletable owner(s), "
                             f"{len(badm)} unbuilt module(s) outside the allowlist\n")
            sys.exit(1)
        sys.stdout.write("dead-census: OK\n")


if __name__ == "__main__":
    main()

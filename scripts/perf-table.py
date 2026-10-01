#!/usr/bin/env python3
"""scripts/perf-table.py -- render OVERVIEW section 9 from the raw files of
`scripts/bench-baselines.sh` (task #107).

    scripts/perf-table.py [--overview OVERVIEW.md] [--task ID] [--raw]
                          [--previous DESIGN.md --previous-task ID] DIR

DIR is a `bench-baselines.sh --out` directory: the per-run
`<bin>-<export>-r<N>.{perf,time,out,exit,load}` files and `identity.json`.
Nothing else is read, and no number in the output is typed into this
script: every number is computed from those files, and every comparison is
a computed percentage.

  --overview FILE   rewrite the region of FILE between
                    `<!-- perf-table:begin -->` and `<!-- perf-table:end -->`
                    (the snapshot paragraph, the table and the comparison
                    paragraph); without it the region is printed
  --task ID         the DESIGN.md task whose section holds the raw block,
                    named in the comparison paragraph (required)
  --raw             also print the raw-numbers block for that DESIGN.md
                    section
  --previous FILE, --previous-task ID
                    with --raw: parse the raw block of an earlier task's
                    section of FILE (this script's own format, which is also
                    task #97-REMEASURE's) and append a per-row comparison

The renderer refuses (exit 1, naming the runs) when any run of the table's
matrix is missing, exited non-zero (a cap, a timeout, a rejection) or has
no instruction count, or when the checkers disagree on what they accepted.
"""

import argparse
import json
import re
import statistics
import sys
import textwrap
from pathlib import Path

ROWS = [  # (bin, table label, raw-block label)
    ("con-ron", "**con-ron**, one worker", "con-ron ×1"),
    ("con-ron-j8", "**con-ron**, eight workers", "con-ron ×8"),
    ("con-leche", "con-leche, one worker", "con-leche ×1"),
    ("nanoda", "nanoda, one worker", "nanoda"),
]
EXPORTS = [("init", "`Init`"), ("mathlib", "Mathlib")]
BUDGET = 3  # CLAUDE.md: a con-ron run may use at most 3x con-leche's memory
BEGIN, END = "<!-- perf-table:begin -->", "<!-- perf-table:end -->"
MINUS = "−"
DASH = "–"


# ---- reading ---------------------------------------------------------------

def read_run(stem):
    def text(ext):
        p = stem.with_name(stem.name + ext)
        return p.read_text(errors="replace") if p.exists() else None

    run = {"name": stem.name}
    ex = text(".exit")
    run["exit"] = int(ex.strip()) if ex and ex.strip().lstrip("-").isdigit() else None
    perf = text(".perf") or ""
    m = re.search(r"^\s*([\d,]+)\s+instructions:u", perf, re.M)
    run["ins"] = int(m.group(1).replace(",", "")) if m else None
    m = re.search(r"^\s*([\d,]+)\s+cycles:u", perf, re.M)
    run["cyc"] = int(m.group(1).replace(",", "")) if m else None
    m = re.search(r"^\s*([\d.]+) seconds time elapsed", perf, re.M)
    run["wall"] = float(m.group(1)) if m else None
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text(".time") or "")
    run["rss"] = int(m.group(1)) if m else None
    out = text(".out") or ""
    m = (re.search(r"accepted (\d+) declarations", out)
         or re.search(r"Checked (\d+) declarations with no errors", out))
    run["decls"] = int(m.group(1)) if m else None
    load = text(".load")
    run["load"] = float(load.split()[0]) if load else None
    return run


def read_matrix(d):
    runs, bad = {}, []
    for b, _, _ in ROWS:
        for e, _ in EXPORTS:
            stems = sorted(
                (p.with_suffix("") for p in d.glob(f"{b}-{e}-r*.exit")
                 if re.fullmatch(rf"{re.escape(b)}-{e}-r\d+", p.stem)),
                key=lambda s: int(s.name.rsplit("-r", 1)[1]))
            rs = [read_run(s) for s in stems]
            if not rs:
                bad.append(f"{b}-{e}: no runs")
            for r in rs:
                if r["exit"] != 0:
                    bad.append(f"{r['name']}: exit {r['exit']}")
                elif None in (r["ins"], r["wall"], r["rss"], r["decls"]):
                    bad.append(f"{r['name']}: incomplete raw files")
            runs[b, e] = rs
    if bad:
        sys.exit("perf-table.py: refusing to render:\n  " + "\n  ".join(bad))
    for e, _ in EXPORTS:
        counts = {r["decls"] for b in ("con-ron", "con-ron-j8", "con-leche")
                  for r in runs[b, e]}
        if len(counts) != 1:
            sys.exit(f"perf-table.py: con-ron and con-leche accepted different "
                     f"declaration counts on {e}: {sorted(counts)}")
        if len({r["decls"] for r in runs["nanoda", e]}) != 1:
            sys.exit(f"perf-table.py: nanoda's runs disagree on {e}")
    return runs


# ---- formatting ------------------------------------------------------------

def grp(n):
    return f"{n:,}".replace(",", " ")


def span(lo, hi, fmt, unit):
    a, b = fmt(lo), fmt(hi)
    return f"{a} {unit}" if a == b else f"{a}{DASH}{b} {unit}"


def pct(x):
    return f"{x * 100:.1f} %"


def signed_pct(x):
    s = f"{abs(x) * 100:.1f} %"
    return ("+" if x >= 0 else MINUS) + s


def gb(kb):
    return f"{kb / 1e6:.2f}"


def short(ident):
    return ident["commit"][:8]


def wrap(text):
    # Keep a number with its unit or its thousands groups, and a code span,
    # on one line: protect those spaces from the wrapper.
    nb = "\x00"
    text = re.sub(r"`[^`]*`", lambda m: m.group(0).replace(" ", nb), text)
    text = re.sub(r"(?<=\d) (?=[\d%GK×s])", nb, text)
    text = re.sub(r"(?<=\d) (?=GB)", nb, text)
    out = textwrap.fill(text, width=76, break_long_words=False,
                        break_on_hyphens=False)
    return out.replace(nb, " ")


# ---- the OVERVIEW region ---------------------------------------------------

def median(rs, k):
    return statistics.median(r[k] for r in rs)


def render_overview(runs, ident, task):
    n_init = runs["con-ron", "init"][0]["decls"]
    n_ml = runs["con-ron", "mathlib"][0]["decls"]
    k_init = {len(runs[b, "init"]) for b, _, _ in ROWS}
    k_ml = {len(runs[b, "mathlib"]) for b, _, _ in ROWS}
    loads = [r["load"] for rs in runs.values() for r in rs if r["load"] is not None]

    p1 = ("Measured with `perf stat -e instructions:u,cycles:u`.  Instruction "
          "counts are the measure of record, because they do not depend on "
          "machine load; wall time and peak memory are secondary.  All runs are "
          "`--verified` release builds with mimalloc, on `lean4export` exports "
          f"of Lean's `Init` ({grp(n_init)} declarations) and of Mathlib "
          f"({grp(n_ml)}).  The table is one snapshot, taken on {ident['date']}: "
          f"con-ron at `{short(ident['con-ron'])}`, con-leche at its pin "
          f"`{short(ident['con-leche'])}`, nanoda at `{short(ident['nanoda'])}`.  ")
    k = "/".join(str(x) for x in sorted(k_init))
    p1 += f"`Init` wall time is the range of {k} runs"
    if loads:
        p1 += (" on a shared machine (one-minute load average "
               f"{span(min(loads), max(loads), lambda x: f'{x:.1f}', '').strip()}"
               " at the starts of the runs)")
    else:
        p1 += " on a shared machine"
    if k_ml == {1}:
        p1 += "; Mathlib was run once per checker, so it has no wall-time column."
    else:
        p1 += ("; Mathlib was run " + "/".join(str(x) for x in sorted(k_ml))
               + " times per checker, and its wall time is not reported.")

    head = ("| | `Init` instructions | `Init` wall, peak RSS | "
            "Mathlib instructions | Mathlib peak RSS |\n|---|---:|---|---:|---:|")
    lines = [head]
    for b, label, _ in ROWS:
        ri, rm = runs[b, "init"], runs[b, "mathlib"]
        ins_i = f"{median(ri, 'ins') / 1e9:.2f} G"
        wall_i = span(min(r["wall"] for r in ri), max(r["wall"] for r in ri),
                      lambda x: f"{x:.1f}", "s")
        rss_i = span(min(r["rss"] for r in ri), max(r["rss"] for r in ri), gb, "GB")
        ins_m = f"{grp(round(median(rm, 'ins') / 1e9))} G"
        rss_m = span(min(r["rss"] for r in rm), max(r["rss"] for r in rm), gb, "GB")
        lines.append(f"| {label} | {ins_i} | {wall_i}, {rss_i} | {ins_m} | {rss_m} |")
    table = "\n".join(lines)

    def ratio(a, b, e):
        return median(runs[a, e], "ins") / median(runs[b, e], "ins")

    p2 = ("Single-threaded, con-ron executes "
          f"{pct(ratio('con-ron', 'con-leche', 'init'))} of con-leche's "
          f"instructions on `Init` and {pct(ratio('con-ron', 'con-leche', 'mathlib'))} "
          f"on Mathlib, and {pct(ratio('con-ron', 'nanoda', 'init'))} and "
          f"{pct(ratio('con-ron', 'nanoda', 'mathlib'))} of nanoda's.  "
          "Eight workers change con-ron's instruction count by "
          f"{signed_pct(ratio('con-ron-j8', 'con-ron', 'init') - 1)} on `Init` and "
          f"{signed_pct(ratio('con-ron-j8', 'con-ron', 'mathlib') - 1)} on Mathlib "
          "(medians of the runs throughout).  ")

    # The memory budget, checked: the largest peak of each con-ron row
    # against BUDGET times the smallest con-leche peak on the same export.
    over, worst = [], {}
    for e, ename in EXPORTS:
        cap = BUDGET * min(r["rss"] for r in runs["con-leche", e])
        top = 0
        for b, label, _ in ROWS[:2]:
            peak = max(r["rss"] for r in runs[b, e])
            top = max(top, peak)
            if peak > cap:
                over.append(f"{label.replace('**', '')} on {ename} "
                            f"({gb(peak)} GB against {gb(cap)} GB)")
        worst[e] = (top, cap)
    p2 += (f"CLAUDE.md's memory budget is {BUDGET}× con-leche's peak RSS on the "
           "same export: ")
    if over:
        p2 += "it is exceeded by " + "; ".join(over) + ".  "
    else:
        p2 += ("every con-ron peak is within it (largest peak "
               + ", ".join(f"{gb(worst[e][0])} GB against {gb(worst[e][1])} GB "
                           f"on {ename}" for e, ename in EXPORTS)
               + ").  ")
    p2 += ("`scripts/bench-baselines.sh` runs the measurements and "
           "`scripts/perf-table.py` writes this section from its raw files "
           "(both: `scripts/bench-baselines.sh --build --render --task <id>`); "
           "`scripts/corpus.sh` builds the exports; the raw numbers are in "
           f"DESIGN.md's task {task} section.")

    return "\n\n".join([wrap(p1), table, wrap(p2)])


# ---- the DESIGN raw block --------------------------------------------------

RAW_ROW = re.compile(r"^\| (`Init`|Mathlib) \| ([^|]+?) \| ([^|]+) \| ([^|]+) \| ([^|]+) \|")


def ints(cell):
    return [int(x.replace(" ", "").replace(",", "")) for x in cell.split("/")]


def render_raw(runs, ident):
    out = ["**Identities** (`identity.json`): " + ", ".join(
        f"{k} `{ident[k]['commit']}`{' (dirty)' if ident[k].get('dirty') else ''} "
        f"(md5 `{ident[k]['md5'][:12]}…`)" for k in ("con-ron", "con-leche", "nanoda"))
        + f"; {ident['date']}; {ident.get('nproc', '?')} hardware threads.", ""]
    out.append("| export | checker | instructions:u | wall | peak RSS (KB) "
               "| accepted | load (1 min) |")
    out.append("|---|---|---:|---:|---:|---:|---:|")
    for e, ename in EXPORTS:
        for b, _, raw in ROWS:
            rs = runs[b, e]
            out.append(
                f"| {ename} | {raw} | " + " / ".join(grp(r["ins"]) for r in rs)
                + " | " + " / ".join(f"{r['wall']:.2f}" for r in rs) + " s | "
                + " / ".join(grp(r["rss"]) for r in rs) + " | "
                + grp(rs[0]["decls"]) + " | "
                + " / ".join("?" if r["load"] is None else f"{r['load']:.2f}" for r in rs)
                + " |")
    return "\n".join(out)


def parse_previous(path, task):
    text = Path(path).read_text()
    m = re.search(rf"^### Task {re.escape(task)}\b.*$", text, re.M)
    if not m:
        sys.exit(f"perf-table.py: no section 'Task {task}' in {path}")
    nxt = re.search(r"^### ", text[m.end():], re.M)
    body = text[m.end(): m.end() + nxt.start() if nxt else len(text)]
    prev = {}
    for line in body.splitlines():
        r = RAW_ROW.match(line)
        if r:
            prev[r.group(1), r.group(2).strip()] = (ints(r.group(3)), ints(r.group(5)))
    if not prev:
        sys.exit(f"perf-table.py: no raw rows in section 'Task {task}'")
    return prev


def render_delta(runs, prev, task):
    out = [f"Against task {task}'s raw block (medians; peak RSS is the largest run):", "",
           "| export | checker | instructions:u then | now | change | peak RSS then | now | change |",
           "|---|---|---:|---:|---:|---:|---:|---:|"]
    for e, ename in EXPORTS:
        for b, _, raw in ROWS:
            if (ename, raw) not in prev:
                continue
            pi, pr = prev[ename, raw]
            ni, nr = median(runs[b, e], "ins"), max(r["rss"] for r in runs[b, e])
            a, c = statistics.median(pi), max(pr)
            out.append(f"| {ename} | {raw} | {grp(round(a))} | {grp(round(ni))} | "
                       f"{signed_pct(ni / a - 1)} | {grp(c)} | {grp(nr)} | "
                       f"{signed_pct(nr / c - 1)} |")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("dir")
    ap.add_argument("--overview")
    ap.add_argument("--task", required=True)
    ap.add_argument("--raw", action="store_true")
    ap.add_argument("--previous")
    ap.add_argument("--previous-task")
    a = ap.parse_args()
    d = Path(a.dir)
    ident = json.loads((d / "identity.json").read_text())
    # The table names con-ron's and con-leche's commits, so those must be
    # the binaries' sources.  nanoda's build is a copy with an empty
    # `[workspace]` table appended to its Cargo.toml (DESIGN.md "Task
    # #97-P6-3"), so it is always dirty; the raw block says so.
    for k in ("con-ron", "con-leche"):
        if ident[k].get("dirty"):
            sys.exit(f"perf-table.py: {k} was built from a tree with "
                     "uncommitted changes; commit, rebuild and re-run")
    runs = read_matrix(d)
    region = render_overview(runs, ident, a.task)
    if a.overview:
        p = Path(a.overview)
        text = p.read_text()
        if text.count(BEGIN) != 1 or text.count(END) != 1:
            sys.exit(f"perf-table.py: {p} needs exactly one {BEGIN} … {END}")
        i, j = text.index(BEGIN) + len(BEGIN), text.index(END)
        p.write_text(text[:i] + "\n" + region + "\n" + text[j:])
        print(f"perf-table.py: wrote {p}", file=sys.stderr)
    else:
        print(region)
    if a.raw:
        print()
        print(render_raw(runs, ident))
        if a.previous:
            print()
            print(render_delta(runs, parse_previous(a.previous, a.previous_task),
                               a.previous_task))
        start, end = d / "matrix.start", d / "matrix.end"
        if start.exists() and end.exists():
            s = int(end.read_text()) - int(start.read_text())
            print(f"\nThe matrix ran {s // 3600} h {s % 3600 // 60:02d} min "
                  f"({grp(s)} s).")


if __name__ == "__main__":
    main()

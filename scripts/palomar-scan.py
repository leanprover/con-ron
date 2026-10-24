#!/usr/bin/env python3
"""scripts/palomar-scan.py — con-ron's verdicts on the Palomar registry.

The Palomar registry (github.com/PalomarRegistry/PalomarSubmission) checks
every submission with Lean's kernel and the independent kernels bundled with
the toolchain, con-ron among them.  Each "Verify submission" run uploads a
`mechanical-report-*` artifact whose `mechanical-report.json` records the
verdicts; the run logs do not.  This script downloads those reports (cached,
so a re-run fetches only new runs) and lists every run in which con-ron did
not accept, with what the other kernels said.

Two report shapes record con-ron's verdict:

  * a kernel of `kernels[]`: con-ron's verdict is in `comparator_log_tail`
    ("con-ron kernel rejected the solution"), and a rejection that Lean's
    kernel did not share fails the submission (`palomar.kernel_disagreement`);
  * an entry of `kernel_attempts[]` (since 2026-10-21): `status` is
    `accepted` or `declined`, with a `reason` (`fuel-exhausted`,
    `unsupported-inductive`, `capacity` for the run's time or memory
    ceiling, ...); a decline is recorded and does not block the submission.

    usage: scripts/palomar-scan.py [--since YYYY-MM-DD] [--dir DIR] [--all]

`--since` limits the listing (not the download) to runs created on or after
that date; `--all` lists con-ron's accepting runs as well.  The cache is
`DIR` (default `_tmp/palomar`): `runs.json`, and `reports/<run id>/`, one
directory per run (`none` marks a run without a report).  Needs `gh`.
"""

import argparse
import json
import os
import subprocess
import sys
import zipfile
from concurrent.futures import ThreadPoolExecutor

REPO = "PalomarRegistry/PalomarSubmission"
WORKFLOW = "Verify submission"


def gh(*args, binary=False):
    r = subprocess.run(["gh", *args], capture_output=True, check=False)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)}: {r.stderr.decode(errors='replace').strip()}")
    return r.stdout if binary else r.stdout.decode()


def fetch_report(run_id, rdir):
    """Download run `run_id`'s mechanical report into `rdir`; True if it has one."""
    if os.path.exists(os.path.join(rdir, "done")):
        return True
    if os.path.exists(os.path.join(rdir, "none")):
        return False
    os.makedirs(rdir, exist_ok=True)
    arts = json.loads(gh("api", f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"))
    mech = [a for a in arts["artifacts"] if a["name"].startswith("mechanical") and not a["expired"]]
    if not mech:
        open(os.path.join(rdir, "none"), "w").close()
        return False
    zpath = os.path.join(rdir, "a.zip")
    for attempt in range(3):
        try:
            with open(zpath, "wb") as f:
                f.write(gh("api", f"repos/{REPO}/actions/artifacts/{mech[0]['id']}/zip", binary=True))
            with zipfile.ZipFile(zpath) as z:
                z.extractall(rdir)
            break
        except (RuntimeError, zipfile.BadZipFile):
            if attempt == 2:
                raise
    os.remove(zpath)
    open(os.path.join(rdir, "done"), "w").close()
    return True


def first_line(text, keys=("error", "declined", "rejected")):
    for line in (text or "").splitlines():
        if any(k in line for k in keys):
            return line.strip()
    return (text or "").strip().splitlines()[0] if (text or "").strip() else ""


def con_ron_verdict(rep):
    """(status, reason, detail, others) for con-ron in report `rep`, or None if it did not run."""
    others = []
    tail = rep.get("comparator_log_tail") or ""
    for line in tail.splitlines():
        line = line.strip()
        if line.endswith("the solution") and not line.startswith("con-ron"):
            others.append(line.replace(" kernel ", ": ").replace(" the solution", ""))
    for att in rep.get("kernel_attempts") or []:
        if att.get("name") == "con-ron":
            return (att.get("status"), att.get("reason"), first_line(att.get("detail")), others)
    if "con-ron kernel rejected the solution" in tail:
        return ("rejected", "kernel",
                first_line(tail, ("con-ron: error", "con-ron: declined", "con-ron: rejected")), others)
    if "con-ron kernel accepts the solution" in tail:
        return ("accepted", "", "", others)
    return None


def phase_usage(rep, phase):
    """(seconds, max RSS in KiB) of report `rep`'s resource phase `phase`."""
    for u in rep.get("resource_usage") or []:
        if u.get("phase") == phase:
            return u.get("elapsed_seconds"), u.get("max_rss_kib")
    return None, None


def usage_str(secs, rss):
    return f"{secs:.0f}s {rss // 1024} MB" if secs is not None and rss else "?"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--since", default="")
    ap.add_argument("--dir", default=os.path.join(os.path.dirname(__file__), "..", "_tmp", "palomar"))
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args()
    os.makedirs(os.path.join(a.dir, "reports"), exist_ok=True)

    runs = json.loads(gh("run", "list", "-R", REPO, "-w", WORKFLOW, "-L", "5000",
                         "--json", "databaseId,conclusion,createdAt,status"))
    with open(os.path.join(a.dir, "runs.json"), "w") as f:
        json.dump(runs, f)
    runs = [r for r in runs if r["status"] == "completed" and r["createdAt"] >= a.since]

    def one(r):
        rid = r["databaseId"]
        rdir = os.path.join(a.dir, "reports", str(rid))
        try:
            return r, fetch_report(rid, rdir)
        except RuntimeError as e:
            print(f"warning: run {rid}: {e}", file=sys.stderr)
            return r, False

    with ThreadPoolExecutor(8) as ex:
        fetched = list(ex.map(one, runs))

    ran = 0
    rows = []
    for r, ok in fetched:
        if not ok:
            continue
        path = os.path.join(a.dir, "reports", str(r["databaseId"]), "mechanical-report.json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            rep = json.load(f)
        v = con_ron_verdict(rep)
        if v is None:
            continue
        ran += 1
        status, reason, detail, others = v
        if status == "accepted" and not a.all:
            continue
        src = rep.get("source") or {}
        crc = (rep.get("con_ron_checker") or {}).get("release_tag") or rep.get("lean_toolchain", "")
        rows.append((rep.get("checked_at") or r["createdAt"], src.get("repository", "?"),
                     (src.get("commit") or "")[:8], crc.replace("leanprover/lean4:", ""),
                     rep.get("status", "?"), status, reason or "",
                     usage_str(*phase_usage(rep, "con-ron")),
                     usage_str(*phase_usage(rep, "comparator")),
                     "; ".join(others), detail, r["databaseId"]))

    print(f"{len(runs)} completed runs{' since ' + a.since if a.since else ''}, "
          f"{sum(ok for _, ok in fetched)} with a report, con-ron ran in {ran}, "
          f"{len(rows)} listed\n")
    for (at, repo, commit, tag, sub, status, reason, usage, cusage, others, detail, rid) in sorted(rows):
        print(f"{at[:16]}  {repo} @ {commit}  con-ron of {tag}  submission: {sub}")
        print(f"    con-ron {status} ({reason}), {usage}; others: {others or '-'} "
              f"(the comparator phase: {cusage})")
        if detail:
            print(f"    {detail[:300]}")
        print(f"    https://github.com/{REPO}/actions/runs/{rid}")


if __name__ == "__main__":
    main()

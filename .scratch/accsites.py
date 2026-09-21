import re
import sys

FILES = ["crates/arena-core/src/arena/core.rs",
         "crates/arena-core/src/arena/checker_base.rs",
         "crates/arena-core/src/arena/expr_ops.rs"]

for path in FILES:
    lines = open(path).read().split('\n')
    # find `pub fn NAME(` starts
    starts = [(i, re.match(r'pub fn ([a-z_0-9]+)\(', l)) for i, l in enumerate(lines)]
    starts = [(i, m.group(1)) for i, m in starts if m]
    for k, (i, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = lines[i:end]
        sig = '\n'.join(body[:40])
        for acc in ('acc', 'fvs'):
            if re.search(r'^\s+%s: &Vec<EIdx>,' % acc, sig, re.M):
                uses = [(i + j + 1, l.strip()) for j, l in enumerate(body)
                        if re.search(r'\b%s\b' % acc, l)]
                print("=== %s:%d %s   (%s)" % (path, i + 1, name, acc))
                for ln, t in uses:
                    print("   %6d  %s" % (ln, t[:110]))

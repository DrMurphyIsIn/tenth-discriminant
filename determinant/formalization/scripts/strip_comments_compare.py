#!/usr/bin/env python3
"""Compare two Lean source trees with comments and docstrings removed.

Usage: strip_comments_compare.py <tree A> <tree B>

For every .lean file under either tree, this removes line comments (`-- ...`), block comments
(`/- ... -/`, nested), module docs (`/-! ... -/`) and docstrings (`/-- ... -/`), skipping string
and character literals, and then collapses all whitespace. It prints one line per file (SAME, DIFF,
ONLY-A or ONLY-B) and exits 0 exactly when every file is present in both trees and SAME. The
`scripts/` and `.lake/` directories and the root `lakefile.lean` (which is build configuration, not
a module) are skipped.

This is how we check that the published Lean files differ from the checked ones only in comments and
docstrings. It is a text check; VERIFICATION.md describes the stronger check on the compiled
declarations.
"""

import os
import sys


def strip(src):
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth == 0:
            if c == '"':
                j = i + 1
                while j < n and src[j] != '"':
                    j += 2 if src[j] == '\\' else 1
                out.append(src[i:j + 1])
                i = j + 1
            elif c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == '\\' and i + 3 < n and src[i + 3] == "'")):
                j = i + (4 if src[i + 1] == '\\' else 3)
                out.append(src[i:j])
                i = j
            elif src.startswith("--", i):
                j = src.find("\n", i)
                i = n if j < 0 else j
            elif src.startswith("/-", i):
                depth = 1
                i += 2
            else:
                out.append(c)
                i += 1
        else:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
    return " ".join("".join(out).split())


def lean_files(root):
    acc = set()
    for d, _, fs in os.walk(root):
        parts = os.path.relpath(d, root).split(os.sep)
        if ".lake" in parts or parts[0] == "scripts":
            continue
        for f in fs:
            rel = os.path.relpath(os.path.join(d, f), root)
            if f.endswith(".lean") and rel != "lakefile.lean":
                acc.add(rel)
    return acc


def main():
    a, b = sys.argv[1], sys.argv[2]
    fa, fb = lean_files(a), lean_files(b)
    ok = True
    for rel in sorted(fa | fb):
        if rel not in fb:
            print("ONLY-A", rel); ok = False; continue
        if rel not in fa:
            print("ONLY-B", rel); ok = False; continue
        sa = strip(open(os.path.join(a, rel), encoding="utf-8").read())
        sb = strip(open(os.path.join(b, rel), encoding="utf-8").read())
        same = sa == sb
        ok &= same
        print("SAME  " if same else "DIFF  ", rel)
    print("ALL SAME" if ok else "NOT ALL SAME")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

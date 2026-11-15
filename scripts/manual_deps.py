#!/usr/bin/env python3
"""manual_deps.py -- environment-level independence check of the manual spec (wave 12b).

Builds every module under Semantics/Manual/ (so its .olean exists), then runs
scripts/ManualIndependence.lean with `lake env lean`, preceded by an `import` of each of those
modules. The Lean script walks the constants the Manual modules define through every constant they
use and fails on any constant outside its allow-list (see the script). This closes the bypasses of
the token scan scripts/manual_independence.py (`open Mips in ... Fp.envOf`, `Mips.Fp.f32Abs`, a model
definition named without a forbidden token), which is kept as a fast pre-check.

Usage: manual_deps.py [ROOT]   (default: the repository containing this script). Exit 0 iff clean.
Python 3 stdlib only.
"""
import os
import subprocess
import sys
import tempfile


def manual_modules(root):
    mods = []
    base = os.path.join(root, "Semantics", "Manual")
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(d, f), root)[:-len(".lean")]
                mods.append(rel.replace(os.sep, "."))
    return sorted(mods)


def main():
    root = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else \
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    mods = manual_modules(root)
    if not mods:
        print("manual_deps: no modules under Semantics/Manual")
        return 1
    b = subprocess.run(["lake", "build"] + mods, cwd=root, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    if b.returncode != 0:
        print(b.stdout[-4000:])
        print(f"manual_deps: lake build of the {len(mods)} Manual modules failed")
        return 1
    body = open(os.path.join(root, "scripts", "ManualIndependence.lean"), encoding="utf-8").read()
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "ManualIndependenceRun.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("".join(f"import {m}\n" for m in mods) + "import Lean\n" + body)
        r = subprocess.run(["lake", "env", "lean", path], cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True)
    out = "\n".join(l for l in r.stdout.splitlines()
                    if "remote URL changed" not in l and not l.lstrip().startswith(("old:", "new:")))
    print(out.replace(path, "ManualIndependence.lean"))
    if r.returncode != 0 or ": error" in r.stdout:
        print("manual_deps: FAIL")
        return 1
    print(f"manual_deps: {len(mods)} Manual modules, clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())

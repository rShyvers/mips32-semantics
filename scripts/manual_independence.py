#!/usr/bin/env python3
"""manual_independence.py -- the independence rule of the manual spec (docs/MANUAL-SPEC.md).

Every file under Semantics/Manual/ may import only Semantics.Word, Semantics.Types,
Semantics.Instruction, Semantics.FpOps and other Semantics.Manual modules, and its code (comments and
strings stripped) may not name:
  * any definition of Semantics/Step.lean or Semantics/State.lean (the model),
  * any definition of Semantics/Types.lean except the type names W32/VAddr/PAddr (State, the masks,
    the constants),
  * decode / encode (the model's decoder), the FCSR helpers of FpOps.lean (fpUpdate, envOf,
    raiseFlags, fpeEnabled, ...), or any identifier ending in `Mask`.
Exit 0 iff clean.  Python 3 stdlib only.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOWED_IMPORTS = {"Semantics.Word", "Semantics.Types", "Semantics.Instruction", "Semantics.FpOps"}
TYPE_NAMES_OK = {"W32", "VAddr", "PAddr"}
FPOPS_FORBIDDEN = {"fpUpdate", "envOf", "raiseFlags", "fpeEnabled", "fcsrTrapPending", "getRM", "setRM",
                   "getEnables", "getCause", "getCauseE", "getFS", "getCC", "setCC", "fpeExcCode",
                   "firValue"}


def strip(src):
    """Remove Lean comments (nested block comments, line comments) and string literals."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1; out.append('""'); continue
        out.append(src[i]); i += 1
    return "".join(out)


def defs_of(path):
    names = set()
    txt = strip(open(path, encoding="utf-8").read())
    for m in re.finditer(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                         r"(?:def|abbrev|theorem|lemma|structure|inductive|instance)\s+([A-Za-z_][\w.']*)",
                         txt, re.M):
        names.add(m.group(1).split(".")[-1])
    return names


def main():
    sem = os.path.join(ROOT, "Semantics")
    forbidden = set()
    forbidden |= defs_of(os.path.join(sem, "Step.lean"))
    forbidden |= defs_of(os.path.join(sem, "State.lean"))
    forbidden |= (defs_of(os.path.join(sem, "Types.lean")) - TYPE_NAMES_OK)
    forbidden |= {"decode", "encode", "State"} | FPOPS_FORBIDDEN
    mdir = os.path.join(sem, "Manual")
    files = []
    for d, _, fs in os.walk(mdir):
        files += [os.path.join(d, f) for f in fs if f.endswith(".lean")]
    if not files:
        print("manual_independence: no files under Semantics/Manual"); return 1
    bad = []
    for p in sorted(files):
        rel = os.path.relpath(p, ROOT)
        txt = strip(open(p, encoding="utf-8").read())
        for m in re.finditer(r"^import\s+(\S+)", txt, re.M):
            mod = m.group(1)
            if mod not in ALLOWED_IMPORTS and not mod.startswith("Semantics.Manual."):
                bad.append(f"{rel}: imports {mod}")
        for ln, line in enumerate(txt.split("\n"), 1):
            if line.startswith("import"):
                continue
            # a definition site names the spec's own declaration
            line = re.sub(r"\b(def|abbrev|theorem|structure|inductive)\s+[\w.']+", r"\1 _", line)
            for mt in re.finditer(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", line):
                tok = mt.group(0)
                if mt.start() > 0 and line[mt.start() - 1] == ".":
                    continue   # `(e).f`: generalized field notation on a spec value
                parts = tok.split(".")
                last = parts[-1]
                # `x.f` / `Manual.Ns.f`: a field or a spec-namespaced name; only the model's own
                # namespaces (`Mips.Fp.*`, `_root_.*`) and unqualified names are checked
                if len(parts) > 1 and parts[0] not in ("Mips", "_root_"):
                    continue
                if last in forbidden or (last.endswith("Mask") and last != "Mask"):
                    bad.append(f"{rel}:{ln}: uses {tok}")
    for b in bad:
        print("INDEPENDENCE", b)
    print(f"manual_independence: {len(files)} files, {len(forbidden)} forbidden names, "
          f"{len(bad)} violation(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""compliance.py -- helper for docs/spec/COMPLIANCE.md (read-only; Python 3 stdlib only).

  compliance.py cp0 [--fields]   every Vol III chapter 9 register section (9.4 .. 9.70): number, title,
                                 printed page and its "Compliance Level:" line; --fields adds the rows of
                                 the field tables that carry R/W + reset-state columns
  compliance.py insns            every entry of the Vol II instruction list (mipsdoc.py list) with the
                                 architecture-level tags printed on its Format lines and its printed pages
  compliance.py counts           the two counts the matrix relies on (register sections, list entries)
  compliance.py check [FILE]     verify that FILE (default docs/spec/COMPLIANCE.md) lists every register
                                 section once (IDs `A9.n`) and every instruction-list entry once, in order
                                 (IDs `D1`..`Dn`, key in backticks); exit status 1 on any mismatch

It imports manuals/mipsdoc.py from the code branch (this docs branch is mounted at <repo>/docs);
the manual texts must have been fetched (manuals/fetch.sh).
Page numbers are PRINTED page numbers, as everywhere else in this repository.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "manuals"))
import mipsdoc  # noqa: E402


def sections(key):
    d = mipsdoc.Doc(key)
    return d, d.sections()


def section_text(d, secs, k):
    """[(printed page, text)] of section k (up to the next section of equal or lower depth)."""
    num, _title, pi, li = secs[k]
    depth = num.count(".")
    end = None
    for s in secs[k + 1:]:
        if s[0].count(".") <= depth:
            end = (s[2], s[3])
            break
    last = end[0] if end else min(pi + 12, len(d.pages) - 1)
    out = []
    for i in range(pi, last + 1):
        lines = d.pages[i].split("\n")
        lo = li if i == pi else 0
        hi = end[1] if end and i == end[0] else len(lines)
        out.append((d.printed[i], "\n".join(lines[lo:hi])))
    return out


def cp0_sections():
    """[(number, title, printed page, compliance text or None)] for 9.4 .. 9.70 of Vol III."""
    d, secs = sections("v3")
    out = []
    for k, s in enumerate(secs):
        if not re.match(r"9\.\d+$", s[0]) or int(s[0].split(".")[1]) < 4:
            continue
        pages = section_text(d, secs, k)
        txt = "\n".join(t for _, t in pages)
        m = re.search(r"Compliance Level:(.*?)(?:\n\s*\n)", txt, re.S)
        out.append((s[0], s[1], pages[0][0], re.sub(r"\s+", " ", m.group(1)).strip() if m else None, txt))
    return out


def cmd_cp0(fields):
    rows = cp0_sections()
    for num, title, pg, lv, txt in rows:
        print(f"{num:5} {title}  [printed p.{pg}]")
        print(f"        Compliance Level: {lv or '(none in the extracted text; read the PDF page)'}")
        if fields:
            for l in txt.split("\n"):
                if re.search(r"\b(R/W|R0|R|W|0)\s{2,}(Undefined|Preset|Externally|[0-9])", l):
                    print("          |", re.sub(r"\s{2,}", " | ", l.strip()))
    print(f"\n{len(rows)} register sections 9.4..9.70")


def insn_entries():
    """[(key, title, 'p.N' or 'p.N-M', [format-line tags])] in the tool's order."""
    d = mipsdoc.Doc("v2")
    idx, order = d.insn_index()
    out = []
    for k in order:
        title, pages = idx[k]
        pp = [d.printed[i] for i in pages]
        txt = "\n".join(d.pages[i] for i in pages)
        m = re.search(r"Format:(.*?)Purpose:", txt, re.S)
        tags = []
        for l in (m.group(1).split("\n") if m else []):
            l = re.sub(r"\s{2,}", " ", l.strip())
            t = re.search(r"(MIPS64.*|MIPS32.*|EJTAG|Assembly [Ii]diom.*|SmartMIPS.*|removed in Release 6.*)$", l)
            if t and t.group(1) not in tags:
                tags.append(t.group(1))
        out.append((k, title, f"p.{pp[0]}" if len(pp) == 1 else f"p.{pp[0]}-{pp[-1]}", tags))
    return out


def cmd_insns():
    rows = insn_entries()
    for k, title, pg, tags in rows:
        print(f"{k:42} {pg:10} {'; '.join(tags) or '(no Format tag extracted: image-only first page)'}")
    print(f"\n{len(rows)} entries")


def cmd_counts():
    print("Vol III 9.4..9.70 register sections:", len(cp0_sections()))
    print("Vol II instruction-list entries:   ", len(insn_entries()))


def cmd_check(path):
    path = path or os.path.join(HERE, "..", "spec", "COMPLIANCE.md")
    text = open(path, encoding="utf-8").read()
    ok = True
    want_a = [s[0] for s in cp0_sections()]
    got_a = re.findall(r"^\| A(9\.\d+) \|", text, re.M)
    if got_a != want_a:
        ok = False
        print("A table mismatch: missing", sorted(set(want_a) - set(got_a)), "extra/duplicate",
              sorted({x for x in got_a if got_a.count(x) != 1 or x not in want_a}))
    want_d = [e[0] for e in insn_entries()]
    got = re.findall(r"^\| D(\d+) \| `([^`]+)` \|", text, re.M)
    got_d = [k for _, k in got]
    ids = [int(i) for i, _ in got]
    if got_d != want_d or ids != list(range(1, len(want_d) + 1)):
        ok = False
        print("D table mismatch: missing", [k for k in want_d if k not in got_d],
              "extra/duplicate", [k for k in got_d if got_d.count(k) != 1 or k not in want_d],
              "order/ids ok:", got_d == want_d and ids == list(range(1, len(want_d) + 1)))
    print(f"A rows {len(got_a)}/{len(want_a)}, D rows {len(got_d)}/{len(want_d)}:", "OK" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "cp0"
    if cmd == "cp0":
        cmd_cp0("--fields" in sys.argv)
    elif cmd == "insns":
        cmd_insns()
    elif cmd == "counts":
        cmd_counts()
    elif cmd == "check":
        sys.exit(cmd_check(sys.argv[2] if len(sys.argv) > 2 else None))
    else:
        sys.exit(__doc__)

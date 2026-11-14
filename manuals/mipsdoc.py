#!/usr/bin/env python3
"""mipsdoc -- fast lookup in the MIPS32 architecture manuals (see README.md, AGENTS.md).

The manuals are reference documents, so lookups are structural first:

  mipsdoc.py insn ADD            the full instruction page(s) for ADD (Vol II)
  mipsdoc.py insn c.eq.s         assembler spellings are mapped (-> C.cond.fmt)
  mipsdoc.py insn ADD --rev 2.50 same, from the historical Release 2 manual
  mipsdoc.py list [REGEX]        every instruction page: mnemonic, title, pages
  mipsdoc.py toc v3 [REGEX]      numbered sections of a volume (v1, v2, v3)
  mipsdoc.py section v3 9.36     the text of one section: exact number, else a
                                 regex on the title (best/shortest title first)
  mipsdoc.py search "exception entry EPC BD delay slot" [-d v3] [-k 5] [--full]
                                 ranked full-text search (BM25 over pages)
  mipsdoc.py grep REGEX [-d v2]  every matching line, with document and page
  mipsdoc.py page v2 123 [-n 2]  page(s) by printed page number
  mipsdoc.py cite v3 87          one-line citation for a printed page
  mipsdoc.py selftest            check the tool against both revisions

Document p754 is the IEEE P754 working-group public DRAFT 1.2.5 (2006-10-04), not the
published IEEE 754 (section/search/grep/page/cite work on it; insn does not).
Documents: v1 / v2 / v3 are the latest revisions (normative). Add --rev 2.50
(insn/list only) or use v2old / v3old / v1r3 / v1r0 for the historical ones.
Output starts each page with "== <document> p.<printed page> (pdf page N) ==" so
it can be cited. Needs only the Python standard library and the .txt files
written by fetch.sh.
"""
import argparse
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

DOCS = {
    "v1": ("MD00082-2B-MIPS32INT-AFP-06.01", "MD00082 Vol I-A Rev 6.01"),
    "v2": ("MD00086-2B-MIPS32BIS-AFP-06.06", "MD00086 Vol II-A Rev 6.06"),
    "v3": ("MD00090-2B-MIPS32PRA-AFP-06.02", "MD00090 Vol III Rev 6.02"),
    "v2old": ("MD00086-2B-MIPS32BIS-AFP-02.50", "MD00086 Vol II Rev 2.50"),
    "v3old": ("MD00090-2B-MIPS32PRA-AFP-02.50", "MD00090 Vol III Rev 2.50"),
    "v1r3": ("MD00082-2B-MIPS32INT-AFP-03.02", "MD00082 Vol I-A Rev 3.02"),
    "v1r0": ("MD00082-2B-MIPS32INT-AFP-00.95", "MD00082 Vol I Rev 0.95"),
    # public working-group DRAFT of what became IEEE 754-2008 (not the published standard)
    "p754": ("IEEE-P754-D1.2.5-2006-10-04", "IEEE P754 Draft 1.2.5 (2006-10-04)"),
}
LATEST = ["v2", "v3", "v1"]


class Doc:
    _cache = {}

    def __new__(cls, key):
        if key not in cls._cache:
            cls._cache[key] = super().__new__(cls)
            cls._cache[key]._ready = False
        return cls._cache[key]

    def __init__(self, key):
        if self._ready:
            return
        self._ready = True
        stem, self.title = DOCS[key]
        self.key = key
        path = os.path.join(HERE, stem + ".txt")
        if not os.path.exists(path):
            sys.exit(f"missing {path}: run ./fetch.sh (needs pdftotext)")
        with open(path, encoding="utf-8", errors="replace") as f:
            self.pages = f.read().split("\f")
        self.printed = self._fill_printed([self._printed(p) for p in self.pages])

    @staticmethod
    def _printed(page):
        """Printed page number from the footer line (the one naming MIPS and a
        revision; the number is at the left or right end, depending on the
        manual and on odd/even pages). Copyright lines after it are skipped."""
        lines = [l for l in page.split("\n") if l.strip()]
        for line in reversed(lines[-4:]):
            # IEEE P754 draft footer: "Page N   Copyright (c) 2006 IEEE ..." (even) or "... Page N" (odd)
            if "IEEE" in line and "Copyright" in line:
                m = re.match(r"^\s*Page\s+(\d+)\s", line) or re.search(r"\sPage\s+(\d+)\s*$", line)
                return int(m.group(1)) if m else None
            if "MIPS" not in line or not re.search(r"Revision|Rev\.|Manual", line):
                continue
            m = re.match(r"^\s*(\d+)\s{2,}\S", line) or re.search(r"\S\s{2,}(\d+)\s*$", line)
            return int(m.group(1)) if m else None
        return None

    @staticmethod
    def _fill_printed(nums):
        """Blank pages have no footer: infer them from their neighbours."""
        out = list(nums)
        for i, n in enumerate(out):
            if n is None:
                j = i - 1
                while j >= 0 and nums[j] is None:
                    j -= 1
                k = i + 1
                while k < len(nums) and nums[k] is None:
                    k += 1
                if j >= 0 and k < len(nums) and nums[k] - nums[j] == k - j:
                    out[i] = nums[j] + (i - j)
        return out

    def label(self, i):
        n = self.printed[i]
        return f"== {self.title} p.{n if n is not None else '?'} (pdf page {i + 1}) =="

    def show(self, i):
        print(self.label(i))
        if not self.pages[i].strip():
            print("[no text was extracted for this page (image-only in the PDF); read the PDF page]")
        print(self.pages[i].rstrip("\n"))
        print()

    # ---- instruction pages (Vol II) -------------------------------------
    _CONT = re.compile(r"\s*(\((cont|con.t)[.)]*\.?\)?|,\s*cont\.?|\(cont\)?)\s*$", re.I)
    _END = re.compile(r"^(Appendix|A\.\d|Chapter \d|Revision History|Table A[-.]\d)")

    @staticmethod
    def _is_mn(s):
        """True for a mnemonic header such as ADD, C.cond.fmt, BC1EQZ BC1NEZ."""
        s = s.strip()
        if not s or len(s) > 40 or not re.match(r"^[A-Z]", s):
            return False
        bare = re.sub(r"\b(cond|condn|fmt|fmt2)\b", "", s)
        return not re.search(r"[a-z]", bare) and not re.search(r"\s{2,}", s)

    def _page_head(self, page):
        """(mnemonic string, title, is_continuation) from a page's running
        header, or None. Handles both layouts:
          6.06: 'MNEMONIC      Title'   (header repeated on every page)
          2.50: first line is the bare mnemonic, then 'Title    MNEMONIC';
                continuations read 'Title (cont.)    MNEMONIC'."""
        lines = [l for l in page.split("\n") if l.strip()][:4]
        if not lines:
            return None
        first = lines[0].strip()
        if self._is_mn(first) and "Chapter" not in first:
            title = ""
            for l in lines[1:]:
                parts = [p for p in re.split(r"\s{3,}", l.strip()) if p]
                if len(parts) == 2 and parts[1].strip() == first and not self._is_mn(parts[0]):
                    title = parts[0]
            return first, title, False
        for l in lines:
            parts = [p.strip() for p in re.split(r"\s{3,}", l.strip()) if p.strip()]
            parts = [p for p in parts if p not in ("I", "II")]   # Release-6 change marker
            if len(parts) != 2:
                continue
            for mn, title in ((parts[0], parts[1]), (parts[1], parts[0])):
                if self._is_mn(mn) and re.search(r"[a-z]", title) and not self._is_mn(title) \
                        and not re.match(r"(Table|Figure|Chapter)\b", title) \
                        and "Instruction Set" not in title and "Revision" not in title \
                        and "Instruction Encoding" not in title:
                    cont = bool(self._CONT.search(title))
                    return mn, self._CONT.sub("", title).strip(), cont
        return None

    def insn_index(self):
        """(index, order): index maps the mnemonic string -> (title, [page
        indexes in order]). Pages without a header of their own (table pages in
        the middle of CACHE/PREF) are attached to the preceding instruction
        until a chapter/appendix page ends the instruction chapter."""
        if hasattr(self, "_insn"):
            return self._insn
        idx, order, cur = {}, [], None
        # the instruction chapter starts at the first page with a header AND a
        # "Purpose:" line (the summary tables before it have neither)
        start = next((i for i, p in enumerate(self.pages)
                      if "Purpose:" in p and self._page_head(p)), len(self.pages))
        for i in range(start, len(self.pages)):
            page = self.pages[i]
            first = next((l.strip() for l in page.split("\n") if l.strip()), "")
            if self._END.match(first):
                break                      # Appendix A: bit-encoding tables
            h = self._page_head(page)
            if h is None:
                if cur is not None:
                    idx[cur][1].append(i)
                continue
            mn, title, _cont = h
            if mn not in idx:
                idx[mn] = (title, [])
                order.append(mn)
            elif title and not idx[mn][0]:
                idx[mn] = (title, idx[mn][1])
            idx[mn][1].append(i)
            cur = mn
        # pdftotext sometimes yields an empty page for an instruction's first
        # (graphics-heavy) page; keep it with the instruction so page numbers
        # and `insn` output stay honest (show() says the text is missing).
        for mn in order:
            first = idx[mn][1][0]
            if first > 0 and not self.pages[first - 1].strip() and "Format:" not in self.pages[first]:
                idx[mn][1].insert(0, first - 1)
        self._insn = (idx, order)
        return self._insn

    # ---- numbered sections (Vol I / III, and Vol II chapters) -----------
    _TOC_LINE = re.compile(r"^\s*(\S.*?)\s*\.{4,}\s*(\d+)\s*$")
    _TOC_NUM = re.compile(r"^(?:Chapter\s+(\d+)|Appendix\s+([A-Z])|((?:[A-Z]|\d+)(?:\.\d+)*))[:.]?\s+(\S.*)$")

    def toc_entries(self):
        """[(number, title, printed page)] parsed from the document's own table
        of contents (lines such as '9.36: Cause Register ..... 123')."""
        out = []
        for page in self.pages[:40]:
            for line in page.split("\n"):
                m = self._TOC_LINE.match(line)
                if not m:
                    continue
                n = self._TOC_NUM.match(m.group(1).strip())
                if not n or re.match(r"(Table|Figure)\b", m.group(1)):
                    continue
                num = n.group(1) or n.group(2) or n.group(3)
                if "." not in num and not (n.group(1) or n.group(2)):
                    continue                      # an instruction name such as 'B' or 'J'
                out.append((num, n.group(4).strip().rstrip("."), int(m.group(2))))
        return out

    def sections(self):
        """[(number, title, page index, line index)]: the TOC entries, each
        located at its heading in the body (a left-margin line that starts
        with the number and title; right-aligned running headers are skipped).
        Falls back to a pure body scan if the TOC cannot be parsed."""
        if hasattr(self, "_secs"):
            return self._secs
        toc = self.toc_entries()
        out = []
        self._approx = set()
        if len(toc) >= 20:
            body0 = 1 + max((i for i, p in enumerate(self.pages[:40])
                             if sum(1 for l in p.split("\n") if self._TOC_LINE.match(l)) >= 3), default=10)
            by_page = {}
            for i, n in enumerate(self.printed):
                if n is not None and i >= body0:
                    by_page.setdefault(n, []).append(i)
            pos = 0                                    # headings appear in TOC order
            for num, title, pg in toc:
                cand = [i for p in (pg, pg - 1, pg + 1) for i in by_page.get(p, []) if i >= pos]
                found = self._find_heading(num, title, cand)
                if found:
                    out.append((num, title, found[0], found[1]))
                    pos = found[0]
                elif by_page.get(pg):
                    # heading text lost in extraction: point at the top of its page
                    self._approx.add(len(out))
                    out.append((num, title, by_page[pg][0], 0))
            out = self._merge_scanned(out)
        else:
            out = self._scan_sections()
        self._secs = out
        return out

    def _merge_scanned(self, out):
        """The TOC omits some headings (e.g. 6.5.5 in Vol I). Add body headings
        whose parent section is in the TOC and that sit inside that parent."""
        have = {s[0] for s in out}
        approx = {out[i][0] for i in self._approx}
        extra = []
        for num, title, i, j in self._scan_sections():
            if num in have or "." not in num:
                continue
            parent = num.rsplit(".", 1)[0]
            pk = next((k for k, s in enumerate(out) if s[0] == parent), None)
            if pk is None:
                continue
            nxt = next((s for s in out[pk + 1:] if s[0].count(".") <= parent.count(".")), None)
            lo = (out[pk][2], out[pk][3])
            hi = (nxt[2], nxt[3]) if nxt else (len(self.pages), 0)
            if lo < (i, j) < hi:
                extra.append((num, title, i, j))
                have.add(num)
        merged = sorted(out + extra, key=lambda s: (s[2], s[3]))
        # recompute which entries are approximate (heading position not exact)
        self._approx = {k for k, s in enumerate(merged) if s[0] in approx}
        return merged

    def _find_heading(self, num, title, pages):
        want = re.sub(r"\W+", "", title.lower())[:18]
        for i in pages:
            for j, line in enumerate(self.pages[i].split("\n")):
                if not line.strip() or len(line) - len(line.lstrip()) > 20:
                    continue
                s = line.strip()
                m = re.match(r"^(?:Chapter\s+|Appendix\s+)?" + re.escape(num) + r"[:.]?\s+(.*)$", s)
                if m and re.sub(r"\W+", "", m.group(1).lower()).startswith(want[:14]):
                    return i, j
                if "." not in num and re.match(r"^(Chapter|Appendix)\s+" + re.escape(num) + r"\b", s):
                    return i, j
        return None

    def _scan_sections(self):
        out, seen = [], set()
        for i, page in enumerate(self.pages):
            for j, line in enumerate(page.split("\n")):
                m = re.match(r"^\s{0,12}((?:[A-Z]|\d+)(?:\.\d+){1,4})\s{1,4}([A-Z][^.]{2,}.*)$", line)
                if not m or "...." in line or re.search(r"\s{6,}", line.strip()):
                    continue
                num, title = m.group(1), m.group(2).strip()
                if len(title) > 110 or (num, title) in seen:
                    continue
                seen.add((num, title))
                out.append((num, title, i, j))
        return out


def _expand_braces(name):
    """'B{LE,GE}ZALC' -> ['BLEZALC', 'BGEZALC']."""
    m = re.search(r"\{([^}]*)\}", name)
    if not m:
        return [name]
    return [name[:m.start()] + alt + name[m.end():] for alt in m.group(1).split(",")]


def norm_mnemonic(q):
    """Map an assembler spelling to candidate instruction-page names (all
    upper case; compare case-insensitively). Most specific first."""
    u = q.strip().upper()
    cands = [u]
    m = re.match(r"^C\.[A-Z]+\.(S|D|PS)$", u)
    if m:
        cands.append("C.COND.FMT")
    if re.match(r"^CMP\.[A-Z]+\.(S|D)$", u):
        cands.append("CMP.CONDN.FMT")
    m = re.match(r"^(.+)\.(S|D|W|L|PS)$", u)       # add.s, cvt.d.w, round.w.d, mov.d ...
    if m:
        cands.append(m.group(1) + ".FMT")
    if u.endswith(".HB"):                           # jr.hb / jalr.hb on pages that merge them
        cands.append(u[:-3])
    aliases = {"MOVE": "ADDU", "LI": "ADDIU", "LA": "LUI", "BEQZ": "BEQ", "BNEZ": "BNE",
               "NEG": "SUB", "NEGU": "SUBU", "NOT": "NOR", "NOP": "NOP", "SLLV": "SLLV",
               "B": "B", "BAL": "BAL", "MFC0": "MFC0", "MTC0": "MTC0"}
    if u in aliases:
        cands.append(aliases[u])
    return cands


def lookup_names(order):
    """lower-case name -> index key, for each full key and each mnemonic inside
    a merged key such as 'MUL MUH MULU MUHU' or 'B{LE,GE}ZALC'. Full keys win."""
    names = {}
    for k in order:
        names.setdefault(k.lower(), k)
    for k in order:
        for part in re.split(r"\s+", k):
            for name in _expand_braces(part):
                for n in name.split(","):
                    names.setdefault(n.strip().lower(), k)
    return names


def resolve_insn(d, name):
    idx, order = d.insn_index()
    names = lookup_names(order)
    for c in norm_mnemonic(name):
        k = names.get(c.lower())
        if k:
            return k, idx[k]
    return None, None


def cmd_insn(a):
    d = Doc("v2old" if a.rev == "2.50" else "v2")
    idx, order = d.insn_index()
    k, ent = resolve_insn(d, a.name)
    if k:
        for i in ent[1]:
            d.show(i)
        return
    import difflib
    names = lookup_names(order)
    base = re.sub(r"\.(s|d|w|l|ps)$", "", a.name.strip().lower())
    near = difflib.get_close_matches(a.name.lower(), list(names), n=6, cutoff=0.5)
    near += [n for n in names if n.startswith(base[:3]) and n not in near][:6]
    near = list(dict.fromkeys(names[n] for n in near))[:8]
    sys.exit(f"no instruction page for {a.name!r} in {d.title}. Closest: {', '.join(near) or 'none'}"
             f"  (try: mipsdoc.py list {base[:3]})")


def cmd_list(a):
    d = Doc("v2old" if a.rev == "2.50" else "v2")
    idx, order = d.insn_index()
    for k in order:
        title, pages = idx[k]
        if a.pattern and not re.search(a.pattern, k + " " + title, re.I):
            continue
        pp = [d.printed[i] for i in pages]
        rng = f"{pp[0]}" if len(pp) == 1 else f"{pp[0]}-{pp[-1]}"
        print(f"{k:16} {title:60} p.{rng}")


def cmd_toc(a):
    d = Doc(a.doc)
    for num, title, i, _ in d.sections():
        if a.pattern and not re.search(a.pattern, num + " " + title, re.I):
            continue
        print(f"{num:10} {title[:90]:90} p.{d.printed[i]}")


def _rank_sections(secs, q):
    """Indexes of the sections matching q: exact number first; otherwise a
    title regex, best first (exact title, then title prefix, then shortest)."""
    ql = q.strip().lower()
    num = re.sub(r"^(chapter|appendix|section)\s+", "", ql)
    exact = [k for k, s in enumerate(secs) if s[0].lower() == num]
    if exact:
        return exact
    if re.fullmatch(r"[a-z]?\d*(\.\d+)*", num):         # looks like a number: prefix match
        return [k for k, s in enumerate(secs) if s[0].lower().startswith(num + ".")][:1]
    try:
        rx = re.compile(q, re.I)
    except re.error:
        rx = re.compile(re.escape(q), re.I)
    hits = [k for k, s in enumerate(secs) if rx.search(s[1])]

    def key(k):
        t = re.sub(r"\s*\(.*?\)\s*", " ", secs[k][1]).strip().lower()
        return (t != ql, not t.startswith(ql), len(t), k)
    return sorted(hits, key=key)


def cmd_section(a):
    d = Doc(a.doc)
    secs = d.sections()
    hits = _rank_sections(secs, a.query)
    if not hits:
        sys.exit(f"no section matching {a.query!r} in {d.title}; try: mipsdoc.py toc {a.doc} PATTERN")
    if len(hits) > 1 and not a.all:
        print("several sections match; showing the best. Others (give the number to pick one):")
        for k in hits[1:12]:
            print(f"   {secs[k][0]} {secs[k][1]}")
        print()
    k = hits[0]
    num, title, pi, li = secs[k]
    depth = num.count(".")
    end = None
    for j, s in enumerate(secs[k + 1:], k + 1):
        if s[0].count(".") <= depth and j not in d._approx:
            end = (s[2], s[3])
            break
    last = end[0] if end else min(pi + 12, len(d.pages) - 1)
    if k in d._approx:
        print(f"[note: the heading text of {num} is missing from the extraction; starting at the top of its page]")
    for i in range(pi, last + 1):
        lines = d.pages[i].split("\n")
        lo = li if i == pi else 0
        hi = end[1] if end and i == end[0] else len(lines)
        body = "\n".join(lines[lo:hi]).rstrip("\n")
        if sum(1 for l in body.split("\n") if l.strip()) > (1 if i > pi else 0):
            print(d.label(i))
            print(body)
            print()


_STOP = set("a an the of in on to is are be by for and or with as at it its this that from what how when which "
            "does do not no if then than into".split())


def _stem(t):
    for suf in ("ing", "ed", "es", "s"):
        if t.endswith(suf) and len(t) - len(suf) >= 4 and not t.endswith("ss"):
            return t[: -len(suf)]
    return t


def tokens(s):
    """Lower-case word tokens, light stemming; keeps FCSR, LLbit, c.eq.s,
    BadVAddr, 2^31 (as '2', '31') and the like as single useful tokens."""
    toks = re.findall(r"[a-z0-9_]+(?:\.[a-z0-9_]+)*", s.lower())
    return [_stem(t) for t in toks]


def _head_text(page):
    """Running header + left-margin headings of a page: the words that say
    what the page is about (used for a ranking bonus)."""
    out = []
    for n, line in enumerate(page.split("\n")):
        if not line.strip():
            continue
        s = line.strip()
        indent = len(line) - len(line.lstrip())
        if n < 3 or (indent <= 12 and re.match(r"^(\d+(\.\d+)+|[A-Z]\.\d+(\.\d+)*)\s+\S", s)) \
                or re.match(r"^(Table|Figure) \d+[.-]\d+ ", s):
            out.append(s)
        if len(out) > 8:
            break
    return " ".join(out)


def _is_toc_page(page):
    return sum(1 for l in page.split("\n") if "......" in l) >= 5 or "Revision History" in page[:400]


def rank_pages(query, keys):
    """[(score, Doc, page index)] best first. BM25 over pages, scaled by the
    fraction of query terms present, plus a bonus for terms in the page header."""
    qraw = tokens(query)
    q = [t for t in qraw if t not in _STOP] or qraw
    scored = []
    for key in keys:
        d = Doc(key)
        toks = [tokens(p) for p in d.pages]
        n = len(toks)
        avg = sum(map(len, toks)) / max(n, 1)
        qs = set(q)
        df = {t: sum(1 for p in toks if t in p) for t in qs}
        idf = {t: math.log(1 + (n - df[t] + 0.5) / (df[t] + 0.5)) for t in qs}
        for i, p in enumerate(toks):
            if not p or _is_toc_page(d.pages[i]):
                continue
            tf = {}
            for t in p:
                if t in qs:
                    tf[t] = tf.get(t, 0) + 1
            if not tf:
                continue
            s = 0.0
            for t, f in tf.items():
                s += idf[t] * f * 2.2 / (f + 1.2 * (0.25 + 0.75 * len(p) / avg))
            s *= (len(tf) / len(qs)) ** 2
            head = set(tokens(_head_text(d.pages[i])))
            s += 0.8 * sum(idf[t] for t in qs & head)
            scored.append((s, d, i))
    scored.sort(key=lambda x: -x[0])
    return scored, q


def cmd_search(a):
    scored, q = rank_pages(a.query, [a.doc] if a.doc else LATEST)
    for s, d, i in scored[: a.k]:
        if a.full:
            d.show(i)
            continue
        print(f"{d.label(i)}  score {s:.1f}")
        head = next((l.strip() for l in d.pages[i].split("\n") if l.strip()), "")
        print(f"   [{re.sub(r'\\s{2,}', ' | ', head)[:110]}]")
        shown = 0
        for line in d.pages[i].split("\n")[1:]:
            if any(t in tokens(line) for t in q) and line.strip():
                print("   " + line.strip()[:150])
                shown += 1
                if shown == a.lines:
                    break
        print()
    if not scored:
        print("no match")


def cmd_grep(a):
    keys = [a.doc] if a.doc else LATEST
    rx = re.compile(a.regex, 0 if a.case else re.I)
    n = 0
    for key in keys:
        d = Doc(key)
        for i, page in enumerate(d.pages):
            for line in page.split("\n"):
                if rx.search(line):
                    print(f"{key} p.{d.printed[i]}: {line.strip()[:170]}")
                    n += 1
                    if n >= a.max:
                        print(f"... stopped at {a.max} matches (raise with -m)")
                        return


def cmd_page(a):
    d = Doc(a.doc)
    hits = [i for i, n in enumerate(d.printed) if n == a.number]
    if not hits:
        sys.exit(f"no printed page {a.number} in {d.title}")
    for i in hits[:1]:
        for j in range(i, min(i + a.count, len(d.pages))):
            d.show(j)


def cmd_cite(a):
    """One-line citation for a printed page, e.g. for a docs/spec reference."""
    d = Doc(a.doc)
    hits = [i for i, n in enumerate(d.printed) if n == a.number]
    if not hits:
        sys.exit(f"no printed page {a.number} in {d.title}")
    i = hits[0]
    head = next((re.sub(r"\s{2,}", " | ", l.strip()) for l in d.pages[i].split("\n") if l.strip()), "")
    print(f"{d.title}, printed p.{a.number} (pdf page {i + 1}) [{head[:80]}]")


# ---- self-test ----------------------------------------------------------
def _run(fn, *args):
    """Run a command function, capturing stdout; returns (text, exit message)."""
    import contextlib
    import io
    buf = io.StringIO()
    err = None
    try:
        with contextlib.redirect_stdout(buf):
            fn(argparse.Namespace(**args[0]))
    except SystemExit as e:
        err = str(e.code) if e.code else None
    return buf.getvalue(), err


def cmd_selftest(a):
    need = {k: os.path.join(HERE, DOCS[k][0] + ".txt") for k in DOCS}
    missing = [os.path.basename(p) for p in need.values() if not os.path.exists(p)]
    if missing:
        print("SKIP: extracted text files not present (run ./fetch.sh, needs pdftotext): " + ", ".join(missing))
        return
    results = []

    def check(name, ok, detail=""):
        results.append(ok)
        print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"   [{detail}]" if detail and not ok else ""))

    # instruction pages: (assembler name, rev, [printed pages], phrase)
    insn = [
        ("ERET", "6.06", [177, 178], "LLbit"), ("add.s", "6.06", [34], "ADD.fmt"),
        ("c.eq.s", "6.06", [110, 111, 112, 113], "C.cond.fmt"), ("c.lt.d", "6.06", [110, 111, 112, 113], "less"),
        ("MTC0", "6.06", [290, 291], "MTC0"), ("mfc0", "6.06", [266], "MFC0"),
        ("JALR", "6.06", [196, 197], "JALR"), ("jalr.hb", "6.06", [198, 199, 200], "JALR.HB"),
        ("jr.hb", "6.06", [208, 209, 210], "JR.HB"),
        ("CACHE", "6.06", list(range(114, 122)), "CACHE"), ("SYNCI", "6.06", [412, 413, 414], "SYNCI"),
        ("round.w.d", "6.06", [342], "ROUND.W.fmt"), ("cvt.d.w", "6.06", [153], "CVT.D.fmt"),
        ("cvt.s.w", "6.06", [159], "CVT.S.fmt"), ("cvt.w.d", "6.06", [160], "CVT.W.fmt"),
        ("trunc.w.s", "6.06", [441], "TRUNC.W.fmt"), ("ceil.w.s", "6.06", [128], "CEIL.W.fmt"),
        ("floor.w.d", "6.06", [186], "FLOOR.W.fmt"), ("movf.s", "6.06", [277, 278], "MOVF.fmt"),
        ("mov.s", "6.06", [275], "MOV.fmt"), ("bc1t", "6.06", [60, 61], "BC1T"), ("bc1fl", "6.06", [58, 59], "BC1FL"),
        ("sdc1", "6.06", [362], "SDC1"), ("TGEIU", "6.06", [420], "TGEIU"), ("div", "6.06", [165, 166, 167], "DIV"),
        ("ERET", "2.50", None, "LLbit"), ("ADD", "2.50", None, "overflow"), ("add.s", "2.50", None, "ADD.fmt"),
        ("mtc0", "2.50", [200], "MTC0"), ("c.eq.s", "2.50", [85, 86, 87, 88, 89], "C.cond.fmt"),
        ("CACHE", "2.50", list(range(90, 97)), "CACHE"), ("SYNCI", "2.50", [282, 283, 284], "SYNCI"),
        ("JALR", "2.50", [140, 141], "JALR"), ("jr.hb", "2.50", [147, 148, 149], "JR.HB"),
        ("cvt.d.s", "2.50", [109], "CVT.D.fmt"), ("round.w.s", "2.50", [238, 239], "ROUND.W.fmt"),
        ("movf.s", "2.50", [185, 186], "MOVF.fmt"), ("bc1tl", "2.50", [52, 53], "BC1TL"), ("ldc1", "2.50", None, "LDC1"),
    ]
    for name, rev, pages, phrase in insn:
        d = Doc("v2old" if rev == "2.50" else "v2")
        k, ent = resolve_insn(d, name)
        got = [d.printed[i] for i in ent[1]] if ent else None
        text = "".join(d.pages[i] for i in ent[1]) if ent else ""
        ok = ent is not None and (pages is None or got == pages) and phrase.lower() in text.lower()
        check(f"insn {name} --rev {rev}", ok, f"key={k} pages={got}")
    # index vs the manual's own table of contents
    for key, rev, n in (("v2", "6.06", 263), ("v2old", "2.50", 199)):
        d = Doc(key)
        idx, order = d.insn_index()
        toc = {}
        for page in d.pages[:30]:
            for line in page.split("\n"):
                m = re.match(r"^\s*(\S.*?)\s*\.{4,}\s*(\d+)\s*$", line)
                if m and not re.match(r"(Chapter|Appendix|Table|Figure|\d+(\.\d+)*[:. ]|[A-Z]\.\d)", m.group(1)):
                    toc[m.group(1).strip()] = int(m.group(2))
        bad = [k for k, p in toc.items() if k not in idx or d.printed[idx[k][1][0]] != p]
        extra = [k for k in order if k not in toc]
        check(f"insn index {rev}: {len(order)} entries == TOC ({len(toc)}), same start pages",
              len(order) == len(toc) == n and not bad and not extra, f"bad={bad[:5]} extra={extra[:5]}")
    # sections: (doc, query, phrases that must appear, phrases that must not)
    secs = [
        ("v3", "6.2.3", ["General Exception Processing", "Operation:", "EPC", "endif"], ["6.2.4 Debug"]),
        ("v3", "9.36", ["Cause Register", "ExcCode", "9.36 Cause Register"], ["9.37 NestedExc"]),
        ("v3", "Status Register", ["Status Register", "BEV", "IM7"], []),
        ("v1", "FCSR", ["Rounding mode", "FCSR Register Format", "RM"], ["6.5.5 Floating Point Condition"]),
        ("v1", "6.5.5", ["FCCR", "FCC"], []),
        ("v3old", "Cause Register", ["Cause Register", "ExcCode"], []),
        ("v3old", "8.18", ["Status Register", "BEV"], []),
        ("v1r3", "FCSR", ["Rounding mode", "RM"], []),
    ]
    for key, q, must, mustnot in secs:
        text, err = _run(cmd_section, dict(doc=key, query=q, all=False))
        ok = err is None and all(p in text for p in must) and not any(p in text for p in mustnot)
        check(f"section {key} {q!r}", ok, err or "missing " + str([p for p in must if p not in text]) +
              " unexpected " + str([p for p in mustnot if p in text]))
    # IEEE P754 draft: sections, printed pages (footer "Page N"), citation
    text, err = _run(cmd_section, dict(doc="p754", query="The sign bit", all=False))
    must = ["8.3 The sign bit", "When the sum of two operands with opposite signs",
            "squareRoot(\u20130) shall be \u20130", "exclusive OR of the"]
    check("section p754 'The sign bit'", err is None and all(p in text for p in must) and "p.44" in text,
          err or "missing " + str([p for p in must if p not in text]))
    text, err = _run(cmd_section, dict(doc="p754", query="8.3", all=False))
    check("section p754 '8.3' (by number)", err is None and "8.3 The sign bit" in text and "9.1 Overview" not in text, err or "")
    text, err = _run(cmd_cite, dict(doc="p754", number=44))
    check("cite p754 44", err is None and "IEEE P754 Draft 1.2.5 (2006-10-04), printed p.44" in text, err or text)
    text, err = _run(cmd_page, dict(doc="p754", number=43, count=1))
    check("page p754 43 (odd-page footer)", err is None and "Page 43" in text, err or "")
    text, err = _run(cmd_grep, dict(regex="roundTowardNegative", doc="p754", max=500, case=True))
    check("grep p754 roundTowardNegative hits p.44", err is None and "p754 p.44:" in text, err or "")
    # search: (query, doc or None, expected (doc key, printed page) within the top 3)
    searches = [
        ("value stored in EPC branch delay slot", None, ("v3", 87)),
        ("FCSR rounding mode field RM", None, ("v1", 95)),
        ("LLbit cleared ERET", None, ("v2", 177)),
        ("integer overflow exception ADD", None, ("v2", 33)),
        ("coprocessor unusable CU1", None, ("v3", 100)),
        ("condition code FCC bit 23 25", None, ("v1", 92)),
        ("unaligned load LWL big endian bytes", None, ("v2", 241)),
        ("address error exception BadVAddr", None, ("v3", 177)),
        ("Status BEV exception vector base", None, ("v3", 85)),
        ("default result float to fixed conversion invalid 2^31-1", None, ("v1", 100)),
        ("integer overflow exception ADD", "v2old", ("v2old", 34)),
        ("sign of exact zero sum roundTowardNegative", "p754", ("p754", 44)),
    ]
    for query, doc, (ekey, epage) in searches:
        scored, _ = rank_pages(query, [doc] if doc else LATEST)
        top = [(d.key, d.printed[i]) for _, d, i in scored[:3]]
        check(f"search {query!r}" + (f" -d {doc}" if doc else "") + f" -> {ekey} p.{epage} in top 3",
              (ekey, epage) in top, f"top3={top}")
    failed = results.count(False)
    print(f"\n{len(results) - failed}/{len(results)} checks passed")
    if failed:
        sys.exit(1)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True, metavar="COMMAND")
    rev = dict(choices=["6.06", "2.50"], default="6.06", help="Vol II revision (default 6.06)")
    s = sub.add_parser("insn", help="instruction page(s)"); s.add_argument("name"); s.add_argument("--rev", **rev); s.set_defaults(f=cmd_insn)
    s = sub.add_parser("list", help="list instruction pages"); s.add_argument("pattern", nargs="?"); s.add_argument("--rev", **rev); s.set_defaults(f=cmd_list)
    s = sub.add_parser("toc", help="numbered sections"); s.add_argument("doc", choices=DOCS); s.add_argument("pattern", nargs="?"); s.set_defaults(f=cmd_toc)
    s = sub.add_parser("section", help="text of one section"); s.add_argument("doc", choices=DOCS); s.add_argument("query", help="section number or title regex"); s.add_argument("--all", action="store_true", help="do not list other matches"); s.set_defaults(f=cmd_section)
    s = sub.add_parser("search", help="ranked full-text search"); s.add_argument("query"); s.add_argument("-d", "--doc", choices=DOCS, help="one document (default: v2, v3, v1)"); s.add_argument("-k", type=int, default=6, help="results (default 6)"); s.add_argument("--lines", type=int, default=4, help="matching lines shown per hit"); s.add_argument("--full", action="store_true", help="print whole pages"); s.set_defaults(f=cmd_search)
    s = sub.add_parser("grep", help="regex over every line"); s.add_argument("regex"); s.add_argument("-d", "--doc", choices=DOCS); s.add_argument("-m", "--max", type=int, default=60); s.add_argument("--case", action="store_true", help="case sensitive"); s.set_defaults(f=cmd_grep)
    s = sub.add_parser("page", help="page by printed number"); s.add_argument("doc", choices=DOCS); s.add_argument("number", type=int); s.add_argument("-n", "--count", type=int, default=1); s.set_defaults(f=cmd_page)
    s = sub.add_parser("cite", help="citation line for a printed page"); s.add_argument("doc", choices=DOCS); s.add_argument("number", type=int); s.set_defaults(f=cmd_cite)
    s = sub.add_parser("selftest", help="run the built-in checks"); s.set_defaults(f=cmd_selftest)
    a = p.parse_args()
    try:
        a.f(a)
        sys.stdout.flush()
    except BrokenPipeError:        # e.g. piped into `head`: exit quietly
        try:
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except OSError:
            pass
        sys.exit(0)


if __name__ == "__main__":
    main()

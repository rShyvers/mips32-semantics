#!/usr/bin/env python3
"""trace.py -- generate docs/TRACE.md, the instruction traceability matrix.

docs/ is the `documentation` branch mounted as a worktree (git worktree add docs documentation); the code
branch's gate runs only --check (code-side coverage) and --check-readme; docs/check.sh checks TRACE.md.

    python3 scripts/trace.py [--out PATH] [--json PATH] [--check]
    python3 scripts/trace.py --readme | --check-readme | --write-readme
    (a plain run that writes docs/TRACE.md also refreshes the README's generated block)

For every constructor of `inductive Instruction` (Semantics/Instruction.lean)
the matrix follows one instruction end to end:

    manual page -> INSTRUCTION-REF entry -> decode / encode clause
      -> execInstr arm -> spec theorem(s) -> tests

Everything is derived from the files at run time (no line numbers or
instruction lists are hard-coded), by plain text scanning -- no Lean is run.
Python 3 standard library only.  Each heuristic is documented on the function
that implements it; the main weak spots are repeated in the generated Gaps
section and in the module-level notes below.

Heuristics at a glance
  * mnemonic   : an assembler literal in Semantics/Asm.lean or Semantics/Asm/*.lean (or a backticked
                 token of the constructor's docstring) that equals the
                 constructor name once dots are removed and case is ignored
                 (`cEqS` ~ `c.eq.s`).  Otherwise a camel-case split, marked '?'.
  * manual     : manuals/mipsdoc.py (`resolve_insn`), Rev 6.06,
                 falling back to Rev 2.50 for instructions the newer manual
                 dropped.  Needs the gitignored .txt files (fetch.sh).
  * REF entry  : '###' heading naming the mnemonic > table row whose first
                 cell starts with the mnemonic > backticked mention in a
                 heading > prose mention only (weak, reported as a gap).
  * decode /   : first clause mentioning `.ctor` in the `decode*` / `encode*`
    encode       definitions of Instruction.lean.
  * step       : arm header `  | .ctor ...  =>` (2-space indent) in the
                 `exec*` definitions of Semantics/Exec/*.lean (one table per
                 family, dispatched by Step.lean's `execTables`) and Step.lean;
                 one arm may list several constructors.
  * theorems   : `theorem`/`lemma` under Semantics/Specs/ whose *header*
                 (up to `:= by`) has a `decode .. = some (.ctor ..)`
                 hypothesis.  Primary = named `<ctor>_spec_raw`/`<ctor>_spec`.
  * tests      : first token of each instruction line (comments and labels
                 stripped) of tests/{corpus,equiv,asm,oracle}/*.asm; the idioms
                 with one fixed expansion count as that instruction (`move`/`nop`
                 as addu/sll, `lui` as aui, `jr`/`jr.hb` as jalr/jalr.hb, `b` as
                 beq).  `li`/`la` expansions are data-dependent and not counted.
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INSTR_LEAN = "Semantics/Instruction.lean"
STEP_LEAN = "Semantics/Step.lean"
EXEC_GLOB = "Semantics/Exec/*.lean"
ASM_LEAN = "Semantics/Asm.lean"
ASM_GLOB = "Semantics/Asm/*.lean"
REF_MD = "docs/spec/INSTRUCTION-REF.md"
MANUAL_DIR = os.path.join(ROOT, "manuals")
TEST_DIRS = ["tests/corpus", "tests/equiv", "tests/asm", "tests/oracle"]
DIFF_DIR = "tests/corpus"          # the MARS differential corpus
ORACLE_DIR = "tests/oracle"        # the QEMU differential oracle programs
PSEUDO_AS = {"move": "addu", "nop": "sll", "lui": "aui", "jr": "jalr", "jr.hb": "jalr.hb",
             "b": "beq"}   # idioms with one fixed expansion
CTOR = r"(?<![\w.'])\.{n}(?![\w'])"          # `.name` as a constructor reference


# ---------------------------------------------------------------- file helpers

def read_lines(rel):
    """Lines of a repo-relative file ([] when missing)."""
    try:
        with open(os.path.join(ROOT, rel), encoding="utf-8") as f:
            return f.read().split("\n")
    except OSError:
        return []


def strip_comments(lines):
    """Blank out Lean comments (`--`, nested `/- -/`, docstrings) and string
    literals, preserving line count and columns, so code can be searched
    without false hits.  Strings are only tracked within one line so a stray
    quote cannot desynchronise the rest of the file."""
    out, depth = [], 0
    for line in lines:
        buf, i, in_str = [], 0, False
        while i < len(line):
            two = line[i:i + 2]
            if depth:
                if two == "/-":
                    depth += 1; i += 2; buf.append("  "); continue
                if two == "-/":
                    depth -= 1; i += 2; buf.append("  "); continue
                buf.append(" "); i += 1; continue
            if in_str:
                if line[i] == "\\":
                    buf.append("  "); i += 2; continue
                if line[i] == '"':
                    in_str = False
                buf.append(" " if line[i] != '"' else '"'); i += 1; continue
            if two == "/-":
                depth += 1; i += 2; buf.append("  "); continue
            if two == "--":
                buf.append(" " * (len(line) - i)); break
            if line[i] == '"':
                in_str = True
            buf.append(line[i]); i += 1
        out.append("".join(buf))
    return out


TOP_CMD = re.compile(r"^(/--|/-!|theorem|lemma|def|private|protected|namespace|end|section|open|"
                     r"@\[|example|instance|abbrev|noncomputable|macro|local|attribute|set_option|"
                     r"#|variable|universe|inductive|structure|class|syntax|elab|import|deriving)")


def top_level_decls(lines, kinds):
    """Split a file into top-level declarations of the given kinds
    (`theorem`, `def`, ...).  Returns (kind, name, start_idx, end_idx) where
    the declaration runs from its keyword to the line before the next
    column-0 command."""
    pat = re.compile(r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+|@\[[^\]]*\]\s*)*"
                     r"(%s)\s+([^\s(:{\[]+)" % "|".join(kinds))
    starts = []
    for i, l in enumerate(lines):
        m = pat.match(l)
        if m:
            starts.append((m.group(1), m.group(2), i))
    decls = []
    for k, (kind, name, s) in enumerate(starts):
        e = s + 1
        while e < len(lines) and not TOP_CMD.match(lines[e]):
            e += 1
        decls.append((kind, name, s, e))
    return decls


def link(path, line, label=None):
    """Markdown link from docs/TRACE.md to `path#Lline`, shown as base:line."""
    return f"[{label or os.path.basename(path)}:{line}](../{path}#L{line})"


def esc(s):
    return s.replace("|", "\\|")


# ------------------------------------------------------- 1. the constructors

# Marker comments of the wave flow (a BEGIN/END line naming a wave, a wave-number note).
# They are not section headers and must never become a family title.
WAVE_MARKER = re.compile(r"^(?:(?:BEGIN|END)\b.*|W\d+[A-Za-z]?\b.*|R6-\d+[A-Za-z]?\b.*)$")


def parse_instruction_inductive():
    """Parse `inductive Instruction`: for each constructor its name, field
    string, docstring (whole text and first line), line, and family.

    Family = first line of the `--` comment block that most recently preceded
    the constructor inside the inductive (the file's own section headers),
    with any trailing parenthetical removed.  Weak spot: a mid-family aside
    comment starts a new family."""
    raw = read_lines(INSTR_LEAN)
    code = strip_comments(raw)
    start = next((i for i, l in enumerate(raw) if re.match(r"^inductive Instruction\b", l)), None)
    if start is None:
        sys.exit(f"no `inductive Instruction` in {INSTR_LEAN}")
    ctors, family, doc, prev_comment = [], "(ungrouped)", [], False
    in_doc = False
    for i in range(start + 1, len(raw)):
        line = raw[i]
        if line and not line[0].isspace():
            break                                   # end of the inductive
        s = line.strip()
        if in_doc:
            doc.append(s)
            if s.endswith("-/"):
                in_doc = False
            continue
        if s.startswith("/--"):
            doc = [s]
            in_doc = not s.endswith("-/")
            continue
        if s.startswith("--"):
            if WAVE_MARKER.match(s[2:].strip()):
                continue                            # wave bookkeeping, never a family
            if not prev_comment:
                family = re.sub(r"\s*[(:.].*$", "", s[2:].strip()) or family
            prev_comment = True
            continue
        prev_comment = False
        m = re.match(r"^\|\s*(\w+)\s*(.*)$", code[i].strip())
        if m:
            text = " ".join(doc)
            text = re.sub(r"^/--\s*|\s*-/$", "", text).strip()
            first = re.split(r"(?<=[.;])\s|\s--", text)[0] if text else ""
            fields = re.sub(r"\s*:\s*W32", "", m.group(2)).strip("() ")
            ctors.append({"name": m.group(1), "fields": fields, "line": i + 1,
                          "doc": text, "doc1": first[:110], "family": family})
            doc = []
    return ctors


# ------------------------------------------------------------- 2. mnemonics

def asm_files():
    """The assembler's source files, repo-relative: the root module and its per-family tables."""
    return [ASM_LEAN] + sorted(os.path.relpath(p, ROOT) for p in glob.glob(os.path.join(ROOT, ASM_GLOB)))


def asm_literals():
    """Every lowercase string literal of the assembler (Asm.lean, Asm/*.lean) that looks like a
    mnemonic, with the file and line of its first occurrence (the encoder tables, the idioms, ...).
    A per-format row `("add." ++ f.sfx, ...)` (Asm/Fpu.lean) yields `add.s` and `add.d`."""
    lits = {}
    for rel in asm_files():
        for i, l in enumerate(read_lines(rel)):
            for m in re.finditer(r'"([a-z][a-z0-9]*(?:\.[a-z0-9]+)*)"', l):
                lits.setdefault(m.group(1), (rel, i + 1))
            for m in re.finditer(r'"([a-z][a-z0-9.]*\.)" \+\+ f\.sfx', l):
                for f in ("s", "d"):
                    lits.setdefault(m.group(1) + f, (rel, i + 1))
    return lits


def camel_guess(name):
    """`roundWS` -> `round.w.s`, `cEqD` -> `c.eq.d`: split before capitals."""
    return ".".join(p.lower() for p in re.findall(r"[a-z0-9]+|[A-Z][a-z0-9]*", name))


def find_mnemonics(ctor, lits):
    """Assembler spellings of a constructor.  Returns (mnemonics, rule).
    Rule 'asm' : an Asm.lean literal equals the name minus dots, ignoring case.
    Rule 'doc' : same test on backticked docstring tokens.
    Rule 'guess': camel-case split, unverified.  Weak spot: a constructor
    whose assembler spelling is not a dot-removal of its name (none today)."""
    key = ctor["name"].lower()
    hits = sorted(m for m in lits if m.replace(".", "") == key)
    if hits:
        return hits, "asm"
    toks = re.findall(r"`([a-z][a-z0-9]*(?:\.[a-z0-9]+)*)`", ctor["doc"])
    hits = sorted({t for t in toks if t.replace(".", "") == key})
    if hits:
        return hits, "doc"
    # R6-6B: a constructor with an operand in its mnemonic (`cmpS` -> `cmp.<condn>.s`): the
    # docstring lists every spelling `<head>.<x>.<tail>` with `<head><tail>` = the name
    hits = sorted({t for t in toks if t.count(".") == 2
                   and (t.split(".")[0] + t.split(".")[2]) == key})
    if hits:
        return hits, "doc"
    return [camel_guess(ctor["name"])], "guess"


# --------------------------------------------------------------- 3. manual

def load_manual():
    """Import mipsdoc.py and open the Rev 6.06 (v2) and Rev 2.50 (v2old)
    Volume II manuals.  Returns None when the text files are not fetched."""
    sys.dont_write_bytecode = True
    sys.path.insert(0, MANUAL_DIR)
    try:
        import mipsdoc
        docs = {}
        for key in ("v2", "v2old"):
            stem = mipsdoc.DOCS[key][0]
            if os.path.exists(os.path.join(MANUAL_DIR, stem + ".txt")):
                docs[key] = mipsdoc.Doc(key)
        if "v2" not in docs:
            return None
        return mipsdoc, docs
    except (ImportError, SystemExit, Exception):   # noqa: BLE001 - tolerate any breakage
        return None


def manual_entry(manual, mnemonics):
    """Page of the first mnemonic that mipsdoc resolves.  Returns a dict
    {key,title,pages,rev} or None.  Uses Rev 6.06; if the instruction is not
    in it, Rev 2.50 (rev field says which).  Weak spot: mipsdoc's own alias
    table decides what counts as found (e.g. `c.eq.s` -> C.cond.fmt)."""
    mipsdoc, docs = manual
    for dkey, rev in (("v2", "6.06"), ("v2old", "2.50")):
        d = docs.get(dkey)
        if d is None:
            continue
        for m in mnemonics:
            key, ent = mipsdoc.resolve_insn(d, m)
            if key:
                pp = [d.printed[i] for i in ent[1] if d.printed[i] is not None]
                rng = "?" if not pp else (str(pp[0]) if pp[0] == pp[-1] else f"{pp[0]}-{pp[-1]}")
                return {"key": key, "title": ent[0], "pages": rng, "rev": rev}
    return None


# ------------------------------------------------- 4. INSTRUCTION-REF.md

def index_reference():
    """Index INSTRUCTION-REF.md by mnemonic.  Four tiers per mnemonic, best
    first: 'heading' (a ### heading's slash-separated names), 'table' (a table
    row whose first cell starts with the mnemonic), 'group' (backticked in a
    #/##/### heading), 'prose' (backticked anywhere in text).  Each hit is
    (tier, line, section heading text)."""
    lines = read_lines(REF_MD)
    idx, section = {}, ""

    def add(m, tier, line):
        idx.setdefault(m, {}).setdefault(tier, (line, section))

    for i, l in enumerate(lines, 1):
        h = re.match(r"^(#{1,4})\s+(.*)$", l)
        if h:
            section = h.group(2).strip()
            if len(h.group(1)) >= 3:
                for part in re.split(r"\s+/\s+", re.sub(r"\s*\(.*$", "", section)):
                    w = part.strip().strip("`").split(" ")[0].lower()
                    if re.fullmatch(r"[a-z][a-z0-9.]*", w):
                        add(w, "heading", i)
            for t in re.findall(r"`([a-z][a-z0-9.]*)`", section):
                add(t, "group", i)
            continue
        if l.startswith("|"):
            cell = l.split("|")[1] if l.count("|") > 1 else ""
            m = re.match(r"\s*`([a-z][a-z0-9.]*)[ `]", cell)
            if m:
                add(m.group(1), "table", i)
        for t in re.findall(r"`([a-z][a-z0-9.]*)`", l):
            add(t, "prose", i)
    return idx


def ref_entry(idx, mnemonics):
    """Best reference hit over all spellings: (tier, line, section) or None."""
    for tier in ("heading", "table", "group", "prose"):
        for m in mnemonics:
            hit = idx.get(m, {}).get(tier)
            if hit:
                return (tier,) + hit
    return None


# -------------------------------------------------- 5/6. decode/encode/step

def defs_matching(lines, code, prefix):
    """Line ranges (0-based, end-exclusive) of top-level `def`s whose name
    starts with `prefix`."""
    return [(s, e) for _k, n, s, e in top_level_decls(code, ["def"]) if n.split(".")[-1].startswith(prefix)]


def clause_lines(code, ranges, names):
    """Map ctor name -> sorted line numbers (1-based) of its first/other
    `.ctor` references inside the ranges (code only, comments stripped)."""
    out = {}
    for n in names:
        pat = re.compile(CTOR.format(n=re.escape(n)))
        hits = [i + 1 for s, e in ranges for i in range(s, e) if pat.search(code[i])]
        if hits:
            out[n] = hits
    return out


def match_arms(code, ranges, indent=2):
    """Map ctor name -> arm line for `match` arms at `indent` spaces.  An arm
    header runs from `  | .a ..` to the `=>`; every `| .ctor` in it counts, so
    `| .beq _ _ _ | .bne _ _ _ =>` yields two constructors."""
    arms = {}
    for s, e in ranges:
        i = s
        while i < e:
            if re.match(r"^ {%d}\| *\." % indent, code[i]):
                hdr, j = code[i], i
                while "=>" not in hdr and j + 1 < e and not re.match(r"^ {%d}\| *\." % indent, code[j + 1]):
                    j += 1; hdr += " " + code[j]
                for m in re.finditer(r"\|\s*\.(\w+)", hdr.split("=>")[0]):
                    arms.setdefault(m.group(1), i + 1)
                i = j
            i += 1
    return arms


# ------------------------------------------------------- 7. spec theorems

def spec_files():
    return sorted(glob.glob(os.path.join(ROOT, "Semantics/Specs/**/*.lean"), recursive=True))


def collect_theorems():
    """All theorem/lemma declarations under Semantics/Specs/**.  Each record:
    name, file, line, header (text before the proof), has_sorry.  Header ends
    at the first `:= by` / `:=`<newline>; `sorry`/`admit` are looked for in
    comment-stripped text.  Weak spot: a statement containing `let x :=` at
    end of line truncates the header early (hypotheses precede it, so
    attribution is unaffected)."""
    out = []
    for path in spec_files():
        rel = os.path.relpath(path, ROOT)
        raw = read_lines(rel)
        code = strip_comments(raw)
        for _k, name, s, e in top_level_decls(code, ["theorem", "lemma"]):
            text = "\n".join(code[s:e])
            hdr = re.split(r":=\s*(?:by\b|\n)", text, maxsplit=1)[0]
            out.append({"name": name, "file": rel, "line": s + 1, "header": hdr,
                        "sorry": bool(re.search(r"\b(sorry|admit)\b", text))})
    return out


REFINE_DIR = "Semantics/Refine"


def collect_refinements():
    """Map `<ctor>` -> (file, line) of `theorem <ctor>_refines` in Semantics/Refine/*.lean (namespace
    `Refine`): the per-instruction refinement of the manual's Operation (`step_eq_manual`)."""
    out = {}
    d = os.path.join(ROOT, REFINE_DIR)
    for fn in sorted(os.listdir(d)):
        if not fn.endswith(".lean"):
            continue
        rel = f"{REFINE_DIR}/{fn}"
        code = strip_comments(read_lines(rel))
        for i, line in enumerate(code):
            m = re.match(r"\s*theorem\s+(\w+)_refines\b", line)
            if m:
                out.setdefault(m.group(1), (rel, i + 1))
    return out


def theorems_for(ctor_names, theorems):
    """Map ctor -> theorems whose header has `decode <w> = some (.ctor ..)`
    (also `Instruction.ctor`, and without `some`).  Shapes with several
    constructors in one hypothesis (disjunctions) count for each."""
    out = {n: [] for n in ctor_names}
    for t in theorems:
        for m in re.finditer(r"decode\b[^:=]*=\s*(?:some\s*)?\(*\s*(?:Instruction)?\.(\w+)", t["header"]):
            if m.group(1) in out and t not in out[m.group(1)]:
                out[m.group(1)].append(t)
    return out


def primary_of(ctor, mnemonics, thms, all_theorems):
    """(primary theorem or None, name-only theorem or None).  Primary is
    `<ctor>_spec_raw` else `<ctor>_spec` (also the dotted mnemonic with `_`)
    among the attributed theorems.  Name-only: such a name exists but has no
    decode hypothesis for this constructor -- a misattribution alarm."""
    stems = [ctor] + [m.replace(".", "_") for m in mnemonics]
    for suffix in ("_spec_raw", "_spec"):
        for st in stems:
            for t in thms:
                if t["name"].split(".")[-1] == st + suffix:
                    return t, None
    for suffix in ("_spec_raw", "_spec"):
        for st in stems:
            for t in all_theorems:
                if t["name"].split(".")[-1] == st + suffix:
                    return None, t
    return None, None


# ---------------------------------------------------------------- 8. tests

def instruction_tokens(text):
    """Instruction mnemonics of an .asm source: for each line, strip `#`
    comments and a leading `label:`, drop directives, take the first token."""
    out = set()
    for l in text.split("\n"):
        l = l.split("#", 1)[0].strip()
        l = re.sub(r"^\w+:\s*", "", l)
        if not l or l.startswith("."):
            continue
        tok = l.split()[0].lower()
        out.add(PSEUDO_AS.get(tok, tok))
    return out


def scan_asm_tests():
    """{dir: {program name: set of mnemonics}} for the test directories."""
    res = {}
    for d in TEST_DIRS:
        progs = {}
        for p in sorted(glob.glob(os.path.join(ROOT, d, "*.asm"))):
            with open(p, encoding="utf-8", errors="replace") as f:
                progs[os.path.basename(p)[:-4]] = instruction_tokens(f.read())
        res[d] = progs
    return res


def guard_statements():
    """Top-level `#guard` / `example` statements of Semantics/*.lean and Semantics/Tests/*.lean, as
    (file, text) with comments stripped.  A statement runs until the next
    column-0 line.  Counted once per statement (not per line)."""
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, "Semantics/*.lean"))
                       + glob.glob(os.path.join(ROOT, "Semantics/Tests/*.lean"))):
        rel = os.path.relpath(path, ROOT)
        code = strip_comments(read_lines(rel))
        i = 0
        while i < len(code):
            if re.match(r"^(#guard|example)\b", code[i]):
                j = i + 1
                while j < len(code) and code[j].strip() and code[j][0].isspace():
                    j += 1
                out.append((rel, "\n".join(code[i:j])))
                i = j
            else:
                i += 1
    return out


# ------------------------------------------------------------- 9. assembly

def git_state():
    """(short hash, dirty?, #changed paths) via rev-parse / status --porcelain."""
    def run(*a):
        try:
            return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True, check=True).stdout
        except (OSError, subprocess.CalledProcessError):
            return None
    h = run("rev-parse", "--short", "HEAD")
    st = run("status", "--porcelain")
    n = len([l for l in (st or "").split("\n") if l.strip()])
    return (h or "unknown").strip(), n > 0, n


def build():
    """Run every analysis and return one record per constructor plus context."""
    ctors = parse_instruction_inductive()
    names = [c["name"] for c in ctors]
    lits = asm_literals()
    manual = load_manual()
    refidx = index_reference()

    ins_lines = read_lines(INSTR_LEAN)
    ins_code = strip_comments(ins_lines)
    dec = clause_lines(ins_code, defs_matching(ins_lines, ins_code, "decode"), names)
    enc = match_arms(ins_code, defs_matching(ins_lines, ins_code, "encode"))
    step = {}
    exec_files = sorted(os.path.relpath(p, ROOT) for p in glob.glob(os.path.join(ROOT, EXEC_GLOB))) + [STEP_LEAN]
    for rel in exec_files:
        lines = read_lines(rel)
        code = strip_comments(lines)
        for n, ln in match_arms(code, defs_matching(lines, code, "exec")).items():
            step.setdefault(n, (rel, ln))

    theorems = collect_theorems()
    by_ctor = theorems_for(names, theorems)
    tests = scan_asm_tests()
    guards = guard_statements()
    refines = collect_refinements()

    rows = []
    for c in ctors:
        n = c["name"]
        mn, rule = find_mnemonics(c, lits)
        pri, name_only = primary_of(n, mn, by_ctor[n], theorems)
        pat = re.compile(CTOR.format(n=re.escape(n)) + "|" + r"Instruction\." + re.escape(n) + r"(?![\w'])")
        def hit(toks, mn=mn):
            # c.cond.<fmt> stands for the sixteen c.<cond>.<fmt> mnemonics
            for m in mn:
                if m.startswith("c.cond."):
                    suf = m[len("c.cond"):]
                    if any(t.startswith("c.") and t.endswith(suf) for t in toks):
                        return True
                elif m in toks:
                    return True
            return False
        used = {d: sorted(p for p, toks in progs.items() if hit(toks))
                for d, progs in tests.items()}
        rows.append({
            **c, "mnemonics": mn, "mnemonic_rule": rule,
            "manual": manual_entry(manual, mn) if manual else None,
            "ref": ref_entry(refidx, mn),
            "decode": dec.get(n), "encode": enc.get(n), "step": step.get(n),
            "theorems": [{"name": t["name"], "file": t["file"], "line": t["line"], "sorry": t["sorry"]}
                         for t in by_ctor[n]],
            "primary": None if pri is None else pri["name"],
            "name_only_theorem": None if name_only is None else
                f'{name_only["name"]} ({name_only["file"]}:{name_only["line"]})',
            "refines": refines.get(n),
            "tests": used,
            "guards": sum(1 for _f, t in guards if pat.search(t)),
        })
    return rows, theorems, manual is not None


def summarize(rows, theorems):
    """Counts for the summary block."""
    return [
        ("constructors", len(rows)),
        ("with manual page", sum(1 for r in rows if r["manual"] and r["manual"]["rev"] == "6.06")),
        ("with INSTRUCTION-REF entry (heading or table row)",
         sum(1 for r in rows if r["ref"] and r["ref"][0] in ("heading", "table"))),
        ("with decode clause", sum(1 for r in rows if r["decode"])),
        ("with encode clause", sum(1 for r in rows if r["encode"])),
        ("with step arm", sum(1 for r in rows if r["step"])),
        ("with primary spec theorem", sum(1 for r in rows if r["primary"])),
        ("with refinement theorem (`Refine.<ctor>_refines`)", sum(1 for r in rows if r["refines"])),
        ("with any differential test (tests/corpus)", sum(1 for r in rows if r["tests"].get(DIFF_DIR))),
        ("with any QEMU-oracle test (tests/oracle/*.asm)", sum(1 for r in rows if r["tests"].get(ORACLE_DIR))),
        ("with sorry in an attributed spec theorem", sum(1 for r in rows if any(t["sorry"] for t in r["theorems"]))),
        ("spec theorems / of which contain sorry (all of Semantics/Specs)",
         f'{len(theorems)} / {sum(1 for t in theorems if t["sorry"])}'),
    ]


def gaps(rows, theorems, have_manual):
    """Mechanically flagged items: list of (category, text)."""
    g = []
    for r in rows:
        n, ref = r["name"], r["ref"]
        where = f'`{n}` ({link(INSTR_LEAN, r["line"])})'
        if r["mnemonic_rule"] == "guess":
            g.append(("Mnemonic is a guess", f'{where}: assumed `{r["mnemonics"][0]}`'))
        if have_manual and not (r["manual"] and r["manual"]["rev"] == "6.06"):
            g.append(("No manual page in Rev 6.06", where + (" (found in Rev 2.50 only)" if r["manual"] else "")))
        if ref is None:
            g.append(("No INSTRUCTION-REF entry", where))
        elif ref[0] in ("group", "prose"):
            g.append(("INSTRUCTION-REF mentions it only in a heading/prose (no entry or table row)",
                      f'{where}: {ref[0]} at {link(REF_MD, ref[1])}'))
        if not r["decode"]:
            g.append(("No decode clause", where))
        if not r["encode"]:
            g.append(("No encode clause", where))
        if not r["step"]:
            g.append(("No step arm", where))
        if not r["theorems"]:
            g.append(("No spec theorem", where))
        elif not r["primary"]:
            extra = f' (name-only candidate without decode hypothesis: {r["name_only_theorem"]})' if r["name_only_theorem"] else ""
            g.append(("No primary `_spec_raw`/`_spec` theorem", where + extra))
        elif r["name_only_theorem"]:
            g.append(("Primary-named theorem lacks decode hypothesis", f'{where}: {r["name_only_theorem"]}'))
        if not r["refines"]:
            g.append(("No refinement theorem `Refine.<ctor>_refines`", where))
        if not r["tests"].get(DIFF_DIR):
            g.append(("No differential test (tests/corpus)", where))
    for t in theorems:
        if t["sorry"]:
            g.append(("Theorem contains `sorry`", f'`{t["name"]}` ({link(t["file"], t["line"])})'))
    return g


def cell_manual(r, have_manual):
    m = r["manual"]
    if not have_manual:
        return "manual not fetched"
    if not m:
        return "none"
    flag = "" if m["rev"] == "6.06" else f' (Rev {m["rev"]} only)'
    return esc(f'{m["key"]} - {m["title"]}, p.{m["pages"]}{flag}')


def cell_ref(r):
    ref = r["ref"]
    if not ref:
        return "none"
    tier, line, sec = ref
    mark = {"heading": "", "table": "table: ", "group": "group: ", "prose": "prose: "}[tier]
    return link(REF_MD, line) + " " + esc(mark + sec[:40])


def cell_lines(path, lines):
    if not lines:
        return "-"
    lines = [lines] if isinstance(lines, int) else lines
    s = link(path, lines[0])
    return s + (f" +{len(lines) - 1}" if len(lines) > 1 else "")


def cell_thms(r):
    if not r["theorems"]:
        return "NONE"
    parts = []
    for t in r["theorems"]:
        s = link(t["file"], t["line"], t["name"])
        if t["name"] == r["primary"]:
            s = f"**{s}**"
        if t["sorry"]:
            s += " SORRY"
        parts.append(s)
    return "<br>".join(parts)


def cell_refines(r):
    if not r["refines"]:
        return "NONE"
    f, line = r["refines"]
    return link(f, line, f'{r["name"]}_refines')


def cell_tests(r):
    parts = []
    for d, label in ((DIFF_DIR, "corpus"), ("tests/equiv", "equiv"), ("tests/asm", "asm"), (ORACLE_DIR, "oracle")):
        p = r["tests"].get(d) or []
        if p:
            parts.append(f'{label}: ' + ", ".join(p[:3]) + (f" +{len(p) - 3}" if len(p) > 3 else ""))
    if r["guards"]:
        parts.append(f'guards: {r["guards"]}')
    return esc("; ".join(parts)) or "none"


def render(rows, theorems, have_manual):
    head, dirty, nchg = git_state()
    o = ["# Instruction traceability matrix", "",
         "> **Generated by `python3 scripts/trace.py` -- do not edit by hand.** "
         "Re-run the script after changing the sources; it writes this file deterministically.", "",
         "Follow one instruction end to end: manual page -> INSTRUCTION-REF entry -> decode/encode clause -> "
         "`execInstr` arm -> spec theorem(s) -> refinement of the manual's Operation (`Refine.<ctor>_refines`) -> tests. Links are `file:line` relative to the repository root.", "",
         "## Generation inputs", "",
         f"- git HEAD: `{head}`, working tree: {'dirty (%d changed paths)' % nchg if dirty else 'clean'}",
         f"- `{INSTR_LEAN}` (constructors, decode, encode), `{EXEC_GLOB}` (step arms, dispatched by `{STEP_LEAN}`), `{ASM_LEAN}` + `{ASM_GLOB}` (mnemonics)",
         f"- `{REF_MD}`; Semantics/Specs/**/*.lean ({len(spec_files())} files, {len(theorems)} theorems)",
         "- Manual: MD00086 Vol II-A Rev 6.06 via `manuals/mipsdoc.py`"
         + ("" if have_manual else " -- **manual not fetched** (run `manuals/fetch.sh`)"),
         "- Tests: " + ", ".join(f"`{d}/*.asm`" for d in TEST_DIRS) + "; `#guard`/`example` statements in Semantics/*.lean and Semantics/Tests/*.lean",
         "", "## Summary", "", "| Measure | Count |", "|---|---|"]
    o += [f"| {k} | {v} |" for k, v in summarize(rows, theorems)]
    o += ["", "Legend: mnemonic marked `?` is a naming-rule guess; **bold** theorem = primary "
          "`<ctor>_spec_raw`/`_spec`; `+N` = further hits; Tests lists the first three programs; "
          "`guards` counts in-file `#guard`/`example` statements.", ""]
    fams = []
    for r in rows:
        if not fams or fams[-1][0] != r["family"]:
            fams.append((r["family"], []))
        fams[-1][1].append(r)
    merged = {}
    for name, rs in fams:
        merged.setdefault(name, []).extend(rs)
    for name, rs in merged.items():
        o += [f"## {name}", "",
              "| Mnemonic | Constructor | Manual (Rev 6.06 page) | INSTRUCTION-REF | decode | encode | step | Spec theorem(s) | Refinement | Tests |",
              "|---|---|---|---|---|---|---|---|---|---|"]
        for r in rs:
            mn = ", ".join(f"`{m}`" for m in r["mnemonics"]) + ("?" if r["mnemonic_rule"] == "guess" else "")
            ctor = link(INSTR_LEAN, r["line"], r["name"])
            o.append("| " + " | ".join([mn, ctor, cell_manual(r, have_manual), cell_ref(r),
                                 cell_lines(INSTR_LEAN, r["decode"]), cell_lines(INSTR_LEAN, r["encode"]),
                                 cell_lines(r["step"][0], r["step"][1]) if r["step"] else "-", cell_thms(r), cell_refines(r),
                                 cell_tests(r)]) + " |")
        o.append("")
    g = gaps(rows, theorems, have_manual)
    o += ["## Gaps", ""]
    if not g:
        o.append("None.")
    cats = {}
    for c, t in g:
        cats.setdefault(c, []).append(t)
    for c, items in cats.items():
        o += [f"### {c} ({len(items)})", ""] + [f"- {t}" for t in items] + [""]
    return "\n".join(o).rstrip() + "\n", g


README = os.path.join(ROOT, "README.md")
README_BEGIN = "<!-- BEGIN GENERATED: trace.py --readme -->"
README_END = "<!-- END GENERATED -->"


def readme_block(rows):
    """Compact per-family coverage table for README.md (no manual access, no git state needed).
    Columns: family, constructors, how many have a primary spec theorem, how many are exercised by a
    tests/corpus program (MARS differential), by a tests/oracle program (QEMU differential), mnemonics."""
    fams = {}
    for r in rows:
        fams.setdefault(r["family"], []).append(r)
    tot = [0, 0, 0, 0]
    o = ["| Family | Constructors | Spec theorem | MARS corpus | QEMU oracle | Mnemonics |",
         "|---|---:|---:|---:|---:|---|"]
    for name, rs in fams.items():
        n = len(rs)
        sp = sum(1 for r in rs if r["primary"])
        mars = sum(1 for r in rs if r["tests"].get(DIFF_DIR))
        orc = sum(1 for r in rs if r["tests"].get(ORACLE_DIR))
        for i, v in enumerate((n, sp, mars, orc)):
            tot[i] += v
        mn = ", ".join(r["mnemonics"][0] for r in rs)
        o.append(f"| {esc(name)} | {n} | {sp} | {mars} | {orc} | {esc(mn)} |")
    o.append(f"| **Total** | **{tot[0]}** | **{tot[1]}** | **{tot[2]}** | **{tot[3]}** | |")
    o += ["", "Columns count constructors of `Instruction`. \"Spec theorem\": has a `<ctor>_spec_raw`/`_spec` theorem. "
          "\"MARS corpus\" / \"QEMU oracle\": the mnemonic occurs as an instruction in a `tests/corpus/*.asm` / "
          "`tests/oracle/*.asm` program (a text scan; it shows the instruction is exercised, not that every behaviour is)."]
    return "\n".join(o)


def readme_text(block):
    """README.md content with the generated block replaced by `block`; None if markers are absent."""
    with open(README, encoding="utf-8") as f:
        t = f.read()
    i, j = t.find(README_BEGIN), t.find(README_END)
    if i < 0 or j < i:
        return None
    return t[:i + len(README_BEGIN)] + "\n" + block + "\n" + t[j:]


def main():
    ap = argparse.ArgumentParser(description="Generate the instruction traceability matrix.")
    ap.add_argument("--out", default=os.path.join(ROOT, "docs/TRACE.md"))
    ap.add_argument("--json", help="also dump the raw data to this path")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if a constructor lacks a step arm, a primary spec theorem or a refinement theorem "
                         "`Refine.<ctor>_refines`, or a spec theorem has sorry")
    ap.add_argument("--readme", action="store_true",
                    help="print the compact per-family coverage table (the block embedded in README.md) and exit")
    ap.add_argument("--check-readme", action="store_true",
                    help="exit 1 if the generated block in README.md differs from fresh output; writes nothing")
    ap.add_argument("--write-readme", action="store_true",
                    help="rewrite the generated block in README.md")
    a = ap.parse_args()
    rows, theorems, have_manual = build()
    if a.readme or a.check_readme or a.write_readme:
        block = readme_block(rows)
        if a.readme:
            print(block)
            return
        fresh = readme_text(block)
        if fresh is None:
            print("README.md: generated-block markers not found", file=sys.stderr)
            sys.exit(1)
        with open(README, encoding="utf-8") as f:
            cur = f.read()
        if a.write_readme:
            with open(README, "w", encoding="utf-8") as f:
                f.write(fresh)
            return
        if cur != fresh:
            print("README.md generated block is stale: run `python3 scripts/trace.py --write-readme`", file=sys.stderr)
            sys.exit(1)
        print("README.md generated block is current")
        return
    text, _g = render(rows, theorems, have_manual)
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, "w", encoding="utf-8") as f:
        f.write(text)
    if a.json:
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump({"constructors": rows, "theorems": [{k: v for k, v in t.items() if k != "header"} for t in theorems]},
                      f, indent=1)
    if os.path.abspath(a.out) == os.path.abspath(os.path.join(ROOT, "docs/TRACE.md")) and not a.check:
        fresh = readme_text(readme_block(rows))      # keep the README block in step with TRACE.md (gate.sh --fix)
        if fresh is not None:
            with open(README, "w", encoding="utf-8") as f:
                f.write(fresh)
    for k, v in summarize(rows, theorems):
        print(f"{k}: {v}")
    bad = [r["name"] for r in rows if not r["step"] or not r["primary"]]
    nore = [r["name"] for r in rows if not r["refines"]]
    sor = [t["name"] for t in theorems if t["sorry"]]
    if bad:
        print("missing step arm or primary theorem:", ", ".join(bad), file=sys.stderr)
    if nore:
        print("missing refinement theorem Refine.<ctor>_refines:", ", ".join(nore), file=sys.stderr)
    if sor:
        print("theorems with sorry:", ", ".join(sor), file=sys.stderr)
    if a.check and (bad or sor or nore):
        sys.exit(1)


if __name__ == "__main__":
    main()

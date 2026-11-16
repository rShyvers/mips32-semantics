#!/usr/bin/env python3
"""Second differential oracle: QEMU (MIPS32 Release 6, mips32r6-generic, little-endian) vs the Lean model.

    scripts/oracle.py                  run every tests/oracle/*.asm on both, compare
    scripts/oracle.py --only NAME      run one (repeatable; NAME without .asm)
    scripts/oracle.py --list           list tests and their directives
    scripts/oracle.py --asm            also run the runnable tests/asm programs (others listed as SKIP with the reason)
    scripts/oracle.py --encodings      assembler-encoding oracle (our assembler vs llvm-mc)
    scripts/oracle.py selftest         check the harness itself
    options: --json OUT.json  --keep  --timeout SEC  --jobs N

Design and limits: scripts/README.md, section "Differential oracle". Python 3 stdlib only.
Exit code: 0 iff no FAIL (declared deviations and `known-model-bug`s are counted, not failures); 2 = tools missing.
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TESTDIR = os.path.join(ROOT, "tests", "oracle")
HARNESS = os.path.join(TESTDIR, "harness", "boot.s")
ENCLIST = os.path.join(TESTDIR, "encodings.list")
ASMDIR_LEAN = os.path.join(ROOT, "Semantics", "Asm")
# Toolchain targets (DECISIONS D1: little-endian Release 6)
QEMU = "qemu-system-mipsel"
QEMU_CPU = "mips32r6-generic"
MC_TRIPLE = "-triple=mipsel-unknown-elf"
MC_CPU = "-mcpu=mips32r6"
LD_EMU = "elf32ltsmip"
BYTEORDER = "little"

# ----------------------------------------------------------------------------- constants
# Comparison masks.  Bits the model implements (Semantics/Types.lean statusWriteMask / causeWriteMask
# plus the exception-entry fields).  Everything else in Status/Cause is hardware state the model
# does not have (Status.SR/NMI/RP/TS/R0/..., Cause.TI/PCI/WP/IP7..IP2 timer+device interrupts).
STATUS_MASK = 0x3440FF17   # CU1(29) RW(28) FR(26, read-only 1, R6-5) BEV(22) IM7..0(15:8) UM(4) ERL(2) EXL(1) IE(0)
CAUSE_MASK = 0xB880037C    # BD(31) CE(29:28) DC(27) IV(23) IP1..0(9:8) ExcCode(6:2)
CU1 = 0x20000000
TEXT_LO, TEXT_HI = 0x00400000, 0x10000000
DATA_LO, DATA_PAGES = 0x10010000, 8
STACK_LO = 0x7FFFE000
KT_LO, KT_HI = 0x80000180, 0x80001000
PAGE = 0x1000
REGS = ["zero", "at", "v0", "v1", "a0", "a1", "a2", "a3", "t0", "t1", "t2", "t3", "t4", "t5", "t6",
        "t7", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "t8", "t9", "k0", "k1", "gp", "sp",
        "fp", "ra"]
SIMPLE_FIELDS = ["fcsr", "status", "cause", "epc", "badvaddr", "errorepc", "pc", "output", "term"]
BUF_WORDS = 73


class HarnessError(Exception):
    """The test cannot be run on the QEMU side (harness limitation or test bug)."""


# ----------------------------------------------------------------------------- tools
def find_tools():
    missing = []
    qemu = shutil.which(QEMU)
    if not qemu:
        missing.append(QEMU + " (apt install qemu-system-mips)")
    llvm = None
    cands = [os.environ.get("ORACLE_LLVM_DIR", ""), "/usr/lib/llvm-21/bin"]
    cands += [d for d in sorted(os.listdir("/usr/lib")) if False]
    for d in cands:
        if d and os.path.exists(os.path.join(d, "llvm-mc")):
            llvm = d
            break
    if llvm is None and shutil.which("llvm-mc"):
        llvm = os.path.dirname(shutil.which("llvm-mc"))
    if llvm is None:
        missing.append("LLVM tools (llvm-mc, ld.lld, llvm-objdump, llvm-objcopy; set ORACLE_LLVM_DIR)")
    else:
        for t in ("llvm-mc", "ld.lld", "llvm-objdump", "llvm-objcopy"):
            if not os.path.exists(os.path.join(llvm, t)):
                missing.append(f"{t} in {llvm}")
    if missing:
        sys.stderr.write("oracle.py: required tools are missing (no silent skips):\n  - "
                         + "\n  - ".join(missing) + "\n")
        sys.exit(2)
    return qemu, llvm


def build_mipsrun():
    exe = os.path.join(ROOT, ".lake", "build", "bin", "MipsRun")
    if os.environ.get("ORACLE_NO_BUILD") != "1":
        r = subprocess.run(["lake", "build", "MipsRun"], cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            sys.stderr.write("oracle.py: `lake build MipsRun` failed:\n" + r.stdout[-2000:] + r.stderr[-2000:])
            sys.exit(2)
    if not os.path.exists(exe):
        sys.stderr.write(f"oracle.py: {exe} not found (run `lake build MipsRun`)\n")
        sys.exit(2)
    return exe


class Env:
    def __init__(self, work, keep, timeout):
        self.qemu, self.llvm = find_tools()
        self.mipsrun = build_mipsrun()
        self.work = work
        self.keep = keep
        self.timeout = timeout
        self.boot_o = None

    def llvm_tool(self, name):
        return os.path.join(self.llvm, name)

    def harness_object(self):
        if self.boot_o is None:
            o = os.path.join(self.work, "boot.o")
            sh([self.llvm_tool("llvm-mc"), MC_TRIPLE, MC_CPU, "-filetype=obj", HARNESS, "-o", o])
            self.boot_o = o
        return self.boot_o


def sh(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        raise HarnessError(f"{os.path.basename(cmd[0])} failed: {(r.stderr or r.stdout)[-800:]}")
    return r


# ----------------------------------------------------------------------------- directives
class Directives:
    def __init__(self):
        self.ignore = set()       # fields skipped (ignore-regs)
        self.unpredictable = {}   # field -> citation
        self.deviation = {}       # field -> reason
        self.model_bug = {}       # field -> "<manual citation> <description>"
        self.expect = []          # (field, value)
        self.max_steps = None
        self.bare = False         # run the model without hosted syscall services (MipsRun --bare)
        self.errors = []
        self.raw = []

    @staticmethod
    def field_norm(tok):
        t = tok.lstrip("$")
        if t in REGS:
            return "gpr:" + t
        if t.isdigit() and int(t) < 32:
            return "gpr:" + REGS[int(t)]
        if re.fullmatch(r"f\d+", t):
            return "fpr:" + t
        if t.startswith("mem:"):
            return "mem:0x%08x" % int(t[4:], 0)
        return t

    @classmethod
    def parse(cls, text):
        d = cls()
        for ln in text.splitlines():
            m = re.match(r"\s*#\s*oracle:\s*(.*\S)\s*$", ln)
            if not m:
                continue
            body = m.group(1)
            d.raw.append(body)
            w = body.split()
            key, args = w[0], w[1:]
            if key == "ignore-regs":
                for a in args:
                    f = cls.field_norm(a)
                    if not f.startswith("gpr:"):
                        d.errors.append(f"ignore-regs: bad register '{a}'")
                    d.ignore.add(f)
            elif key == "known-model-bug":
                if len(args) < 3:
                    d.errors.append("known-model-bug needs '<field> <manual citation> <one-line description>'")
                    continue
                d.model_bug[cls.field_norm(args[0])] = " ".join(args[1:])
            elif key in ("expect-deviation", "unpredictable"):
                if len(args) < 2:
                    d.errors.append(f"{key} needs '<field> <reason/citation>'")
                    continue
                (d.deviation if key == "expect-deviation" else d.unpredictable)[cls.field_norm(args[0])] = " ".join(args[1:])
            elif key == "expect":
                for a in args:
                    mm = re.fullmatch(r"([^=]+)=(.+)", a)
                    if not mm:
                        d.errors.append(f"expect: bad item '{a}'")
                        continue
                    d.expect.append((cls.field_norm(mm.group(1)), int(mm.group(2), 0)))
            elif key == "max-steps":
                d.max_steps = int(args[0])
            elif key == "bare":
                # The model runs without the hosted MARS-style services, so every syscall is the
                # architectural System Call exception.  On QEMU that is only so when the test brings
                # its own .ktext handler (otherwise the harness's default handler emulates the services).
                d.bare = True
                if not re.search(r"^\s*\.ktext\b", text, re.M):
                    d.errors.append("bare needs a .ktext handler (without one the QEMU harness emulates the hosted services)")
            else:
                d.errors.append(f"unknown directive '{key}'")
        return d


def field_matches(pat, field):
    """Directive field `pat` covers record field `field` ('gpr' covers 'gpr:t0', 'mem' covers 'mem:0x..')."""
    return pat == field or (":" not in pat and field.startswith(pat + ":"))


# ----------------------------------------------------------------------------- model side
def run_model(env, path, max_steps, bare=False):
    cmd = [env.mipsrun, "--coverage", "--max-steps", str(max_steps)] + (["--bare"] if bare else []) + [path]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if r.returncode not in (0, 1):
        raise HarnessError(f"MipsRun exit {r.returncode}: {r.stderr[-400:]}")
    try:
        j = json.loads(r.stdout)
    except ValueError:
        raise HarnessError("MipsRun produced no JSON: " + r.stdout[:300])
    if not j.get("assembled"):
        raise HarnessError("model assembler rejected the program: " + str(j.get("error")))
    return j


def in_mem_region(a):
    return DATA_LO <= a < DATA_LO + DATA_PAGES * PAGE or STACK_LO <= a < 0x80000000


def model_record(j):
    f = j["final"]
    h = j["halt"]
    kind = h["kind"]
    rec = {"gpr": list(f["gpr"]), "fcsr": f["fcsr"], "fpr": list(f["fpr"]),
           "status": f["cp0"]["status"], "cause": f["cp0"]["cause"], "epc": f["cp0"]["epc"],
           "badvaddr": f["cp0"]["badvaddr"], "errorepc": f["cp0"]["errorepc"], "pc": f["pc"],
           "output": j["output"]}
    rec["mem"] = {a: w for a, w in j["memory"] if in_mem_region(a)}
    if kind == "exit":
        rec["term"] = "exit"
    elif kind == "unhandled_exception":
        rec["term"] = "unhandled_exception(ExcCode=%d)" % h["code"]
    elif kind == "no_instruction":
        rec["term"] = "no_instruction"
    elif kind == "limit":
        rec["term"] = "limit"
    else:
        rec["term"] = kind
    rec["kind"] = kind
    return rec


# ----------------------------------------------------------------------------- QEMU side
def vpage_list(image):
    text, data, kt = {}, {}, {}
    for a, w in image:
        if TEXT_LO <= a < TEXT_HI:
            text[a] = w
        elif DATA_LO <= a < DATA_LO + DATA_PAGES * PAGE:
            data[a] = w
        elif KT_LO <= a < KT_HI:
            kt[a] = w
        else:
            raise HarnessError("image word at 0x%08x is outside the regions the QEMU harness maps "
                               "(text 0x%x.., data 0x%x..+%dK, .ktext 0x%x..0x%x; .kdata is not supported)"
                               % (a, TEXT_LO, DATA_LO, DATA_PAGES * 4, KT_LO, KT_HI))
    return text, data, kt


def runs(words, base_fn):
    """Group {addr: word} into consecutive runs -> [(vaddr_run_start, phys_kseg0, [words])]."""
    out = []
    for a in sorted(words):
        if out and out[-1][0] + 4 * len(out[-1][2]) == a:
            out[-1][2].append(words[a])
        else:
            out.append([a, base_fn(a), [words[a]]])
    return out


def lo_entry(phys):
    return ((phys >> 12) << 6) | 0x1F      # C=3 D=1 V=1 G=1


def build_qemu_elf(env, model, tdir):
    ini = model["initial"]
    if ini["gpr"][26] != 0 or ini["gpr"][27] != 0:
        raise HarnessError("harness requires initial $k0 = $k1 = 0 (model initial state differs)")
    text, data, kt = vpage_list(model["image"])
    tpages = sorted({a // PAGE for a in text})
    # Running off the end of the text must end in a TLB *refill* (no matching entry: vector 0x80000000,
    # owned by the harness even when the test has its own .ktext handler), not a TLB *invalid* (entry
    # matches, page invalid: general vector 0x80000180 = the test's handler).  So if the last text page is
    # even, map its odd partner too (zero words = nops) so the next entry pair is entirely absent.
    if tpages and tpages[-1] % 2 == 0:
        tpages.append(tpages[-1] + 1)
    if len(tpages) > 8:
        raise HarnessError("text spans more than 8 pages")
    tphys = {p: 0x00100000 + i * PAGE for i, p in enumerate(tpages)}
    # TLB: page 0 (harness scratch), text, data (8 pages), stack (2 pages)
    pages = {0: 0x00310000}
    pages.update({p: ph for p, ph in tphys.items()})
    for i in range(DATA_PAGES):
        pages[DATA_LO // PAGE + i] = 0x00200000 + i * PAGE
    pages[STACK_LO // PAGE] = 0x00300000
    pages[STACK_LO // PAGE + 1] = 0x00301000
    tlb = []
    for vpn2 in sorted({p >> 1 for p in pages}):
        e = [vpn2 << 13, 0, 0]
        for k in (0, 1):
            p = (vpn2 << 1) | k
            if p in pages:
                e[1 + k] = lo_entry(pages[p])
        tlb.append(e)
    if len(tlb) > 16:
        raise HarnessError("needs more than 16 TLB entries")
    while len(tlb) < 16:
        tlb.append([0xC0000000 + len(tlb) * 0x2000, 0, 0])
    status = ini["cp0"]["status"]
    cfg = list(ini["gpr"]) + [0, 0, ini["fcsr"], status, ini["cp0"]["cause"],
                              ini["cp0"]["epc"], ini["cp0"]["errorepc"], ini["pc"], 16] + list(ini["fpr"])
    for e in tlb:
        cfg += e
    # image sections
    secs = []   # (name, kseg0 address, words)
    for a, ph, ws in runs(text, lambda a: 0x80000000 + tphys[a // PAGE] + a % PAGE):
        secs.append((a, ph, ws))
    for a, ph, ws in runs(data, lambda a: 0x80200000 + (a - DATA_LO)):
        secs.append((a, ph, ws))
    for a, ph, ws in runs(kt, lambda a: a):
        secs.append((a, ph, ws))
    s = [".section .cfg,\"a\",@progbits"] + [".word 0x%08x" % (w & 0xFFFFFFFF) for w in cfg]
    for i, (_, _, ws) in enumerate(secs):
        s.append(".section .r%d,\"a\",@progbits" % i)
        s += [".word 0x%08x" % (w & 0xFFFFFFFF) for w in ws]
    # one PT_LOAD per section (ld.lld would otherwise merge them and zero-fill the gaps, which makes
    # QEMU's loader report overlapping ROM regions)
    names = [("refill", ".text.refill", 0x80000000)]
    if not kt:
        names.append(("defvec", ".text.defvec", 0x80000180))
    names += [("boot", ".text", 0x80010000), ("cfg", ".cfg", 0x80020000)]
    for i, (_, ph, ws) in enumerate(secs):
        names.append(("r%d" % i, ".r%d" % i, ph))
    ld = ["ENTRY(_start)", "PHDRS {"] + [" p_%s PT_LOAD;" % n for n, _, _ in names] + ["}", "SECTIONS {"]
    for n, sec, addr in names:
        ld.append(" . = 0x%08x; %s : { *(%s) } :p_%s" % (addr, sec, sec, n))
    ld.append(" /DISCARD/ : { *(.text.defvec) *(.data) *(.got) *(.reginfo) *(.MIPS.abiflags) *(.comment) *(.bss) *(.MIPS.options) }")
    ld.append("}")
    open(os.path.join(tdir, "img.s"), "w").write("\n".join(s) + "\n")
    open(os.path.join(tdir, "t.ld"), "w").write("\n".join(ld) + "\n")
    sh([env.llvm_tool("llvm-mc"), MC_TRIPLE, MC_CPU, "-filetype=obj",
        os.path.join(tdir, "img.s"), "-o", os.path.join(tdir, "img.o")])
    elf = os.path.join(tdir, "t.elf")
    sh([env.llvm_tool("ld.lld"), "-m", LD_EMU, "-T", os.path.join(tdir, "t.ld"),
        env.harness_object(), os.path.join(tdir, "img.o"), "-o", elf, "--no-rosegment", "-z", "norelro"])
    return elf


def run_qemu(env, elf):
    cmd = [env.qemu, "-M", "malta", "-cpu", QEMU_CPU, "-m", "64", "-nographic", "-monitor", "none",
           "-serial", "stdio", "-no-reboot", "-kernel", elf]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=env.timeout, stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        return None
    return r.stdout


def parse_qemu(out):
    try:
        w = [int(x, 16) for x in out.split()]
    except ValueError:
        raise HarnessError("unparsable QEMU output: " + out[:200])
    if len(w) < 3 + BUF_WORDS + 1 or w[0] != 0x4F524331:
        raise HarnessError("bad/short QEMU dump (%d words): %r" % (len(w), out[:200]))
    kind = w[1]
    b = w[2:2 + BUF_WORDS]
    i = 2 + BUF_WORDS
    outlen = w[i]
    i += 1
    if outlen > 8192:
        raise HarnessError("emulated syscall output exceeds 8192 bytes")
    out_s = "".join(chr(x & 0xFF) for x in w[i:i + outlen])
    i += outlen
    mem = {}
    while i < len(w) and w[i] != 0xFFFFFFFF:
        mem[w[i]] = w[i + 1]
        i += 2
    if i >= len(w):
        raise HarnessError("QEMU dump missing end marker")
    rec = {"gpr": b[0:32], "fcsr": b[34], "status": b[35], "cause": b[36],
           "epc": b[37], "badvaddr": b[38], "errorepc": b[39], "pc": b[40], "fpr": b[41:73],
           "output": out_s, "mem": {a: v for a, v in mem.items() if in_mem_region(a)}, "qkind": kind}
    cause = rec["cause"]
    if kind == 0:
        rec["term"] = "exit"
        rec["kind"] = "exit"
    elif kind == 1:
        rec["term"] = "unhandled_exception(ExcCode=%d)" % ((cause >> 2) & 31)
        rec["kind"] = "unhandled_exception"
    elif kind == 2:
        bd = cause >> 31
        epc, bad = rec["epc"], rec["badvaddr"]
        if (bd == 0 and bad == epc) or (bd == 1 and bad == epc + 4):
            rec["term"] = "no_instruction"
            rec["kind"] = "no_instruction"
        else:
            raise HarnessError("guest touched an unmapped page at 0x%08x (EPC 0x%08x): the QEMU harness maps "
                               "only text, data 0x%x..+%dK, stack 0x%x.., page 0 (except 0xE00..)"
                               % (bad, epc, DATA_LO, DATA_PAGES * 4, STACK_LO))
    else:
        raise HarnessError("harness limitation: syscall in the delay slot of an unsupported branch type")
    return rec


def qemu_record(env, model, tdir):
    elf = build_qemu_elf(env, model, tdir)
    out = run_qemu(env, elf)
    if out is None:
        return {"term": "timeout", "kind": "timeout"}
    return parse_qemu(out)


# ----------------------------------------------------------------------------- compare
def masks_for(model, mrec, qrec):
    """Per-field comparison masks, with the reasons documented here and in scripts/README.md."""
    ini = model["initial"]["cp0"]["status"]
    smask = STATUS_MASK
    if not ini & CU1:
        smask &= ~CU1       # harness forces CU1=1 so the FPU works; model's initial Status has CU1 clear
    skip = set()
    kind = mrec["kind"]
    if kind == "no_instruction":
        # QEMU reaches this by running into an unmapped page (TLB refill exception): its
        # Status.EXL/Cause/EPC/BadVAddr/pc describe that refill, the model just stops.
        skip |= {"status", "cause", "epc", "badvaddr", "pc"}
    if kind == "exit":
        # The harness serves `syscall` through a real Syscall exception on QEMU; that overwrites EPC
        # (Cause.ExcCode/BD and Status.EXL are restored/hidden by the dump code, EPC cannot be).
        skip |= {"epc"}
    return {"status": smask, "cause": CAUSE_MASK, "fcsr": model["fcsr_mask"]}, skip


def compare(model, mrec, qrec):
    m, skip = masks_for(model, mrec, qrec)
    diffs = {}

    def put(field, mv, qv):
        if mv != qv:
            diffs[field] = (mv, qv)
    put("term", mrec["term"], qrec["term"])
    if qrec["kind"] == "timeout":
        return diffs
    for i in range(32):
        put("gpr:" + REGS[i], mrec["gpr"][i], qrec["gpr"][i])
    for k in ("epc", "badvaddr", "errorepc", "pc", "output", "status", "cause", "fcsr"):
        if k in skip:
            continue
        mk = m.get(k, 0xFFFFFFFF)
        if k in m:
            put(k, mrec[k] & mk, qrec[k] & mk)
        else:
            put(k, mrec[k], qrec[k])
    for i in range(32):
        put("fpr:f%d" % i, mrec["fpr"][i], qrec["fpr"][i])
    for a in sorted(set(mrec["mem"]) | set(qrec["mem"])):
        put("mem:0x%08x" % a, mrec["mem"].get(a, 0), qrec["mem"].get(a, 0))
    return diffs


def get_field(rec, field, mask_map=None):
    if field.startswith("gpr:"):
        return rec["gpr"][REGS.index(field[4:])]
    if field.startswith("fpr:f"):
        return rec["fpr"][int(field[5:])]
    if field.startswith("mem:"):
        return rec["mem"].get(int(field[4:], 16), 0)
    v = rec[field]
    if mask_map and field in mask_map:
        v &= mask_map[field]
    return v


def judge(model, mrec, qrec, d):
    """-> (verdict, details). verdict in PASS/FAIL/DEVIATION."""
    fails, devs, notes, bugs = [], [], [], []
    for e in d.errors:
        fails.append("directive error: " + e)
    diffs = compare(model, mrec, qrec) if qrec is not None else {}
    mm = {"status": masks_for(model, mrec, qrec)[0]["status"], "cause": CAUSE_MASK, "fcsr": model["fcsr_mask"]}
    # expectations about the MODEL (manual-derived values)
    for f, v in d.expect:
        got = get_field(mrec, f, mm)
        if got != v:
            fails.append("model != manual expectation: %s = 0x%x, expected 0x%x" % (f, got, v))
    if qrec["kind"] == "timeout":
        if mrec["kind"] == "limit":
            return "PASS", ["both did not terminate (model step limit, QEMU timeout): state not compared"]
        return "FAIL", ["QEMU timed out but the model terminated: %s" % mrec["term"]]
    if mrec["kind"] == "limit":
        fails.append("model hit the step limit but QEMU terminated (%s)" % qrec["term"])
    seen_dev, seen_bug = set(), set()
    for f, (mv, qv) in diffs.items():
        if any(field_matches(p, f) for p in d.ignore):
            continue
        up = [p for p in d.unpredictable if field_matches(p, f)]
        if up:
            notes.append("unpredictable, not compared: %s (%s)" % (f, d.unpredictable[up[0]]))
            continue
        mb = [p for p in d.model_bug if field_matches(p, f)]
        if mb:
            seen_bug.add(mb[0])
            bugs.append("%s: model=%s qemu=%s -- KNOWN MODEL BUG: %s" % (f, fmt(mv), fmt(qv), d.model_bug[mb[0]]))
            continue
        dv = [p for p in d.deviation if field_matches(p, f)]
        if dv:
            seen_dev.add(dv[0])
            devs.append("%s: model=%s qemu=%s -- declared: %s" % (f, fmt(mv), fmt(qv), d.deviation[dv[0]]))
        else:
            fails.append("%s: model=%s qemu=%s" % (f, fmt(mv), fmt(qv)))
    for p in d.deviation:
        if p not in seen_dev:
            fails.append("stale deviation declaration '%s': no mismatch occurred" % p)
    for p in d.model_bug:
        if p not in seen_bug:
            fails.append("stale known-model-bug declaration '%s': the mismatch no longer occurs (bug fixed? remove the directive)" % p)
    if fails:
        return "FAIL", fails + bugs + devs + notes
    if bugs:
        return "KNOWN_BUG", bugs + devs + notes
    if devs:
        return "DEVIATION", devs + notes
    return "PASS", notes


def fmt(v):
    if isinstance(v, int):
        return "0x%08x" % v
    return repr(v)


# ----------------------------------------------------------------------------- test runner
ASMDIR = os.path.join(ROOT, "tests", "asm")


# Programs of tests/asm that the harness cannot judge (explicit, reported as SKIP with the reason).
ASM_SKIP = {
    "cp0_identification": "prints Cause/PRId/Config1 after print syscalls: on QEMU every syscall is a real exception (Cause.ExcCode=8 stays visible) and PRId/Config1 are "
                          "implementation constants; the same facts are checked field-wise by tests/oracle/cp0_ident_ebase and mtc0_cause_dc",
}

# Sidecar `# oracle:` directives for tests/asm programs (the programs themselves stay untouched: EquivHarness reads them).
# Release 6 FPU (model and QEMU agree on Status.FR = 1, FCSR.NAN2008 = ABS2008 = 1, the 2008 NaN/conversion results): no sidecar needed for the FPU programs.
_MISALIGNED = ("MD00086 Vol II-A Rev 6.06 LDC1 p.215 / MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Release 6 permits hardware misalignment support or an "
               "Address Error for every misaligned access): an implementation choice; the profile traps (DECISIONS D3, the model), QEMU mips32r6-generic "
               "performs the access")
ASM_DIRECTIVES = {
    "fp_legacy_nan": ["unpredictable fpr:f2 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: 'When possible, this QNaN result is one of the operand QNaN values' "
                      "-- with two NaN operands which one is returned is not specified"],
    "ldc1_doubleword_alignment": ["unpredictable %s %s" % (f, _MISALIGNED)
                                  for f in ("term", "gpr:v0", "epc", "badvaddr", "pc", "status", "cause", "fpr:f2", "fpr:f3")],
}


def asm_unsupported(path):
    """Reason why a tests/asm program cannot run on the QEMU harness, or None (never skipped silently: reported as SKIP)."""
    base = os.path.basename(path)[:-4]
    if base in ASM_SKIP:
        return ASM_SKIP[base]
    src = open(path).read()
    code = [re.sub(r"#.*", "", l).strip() for l in src.splitlines()]
    in_kt, kt_syscall = False, False
    for l in code:
        if re.match(r"\.ktext\b", l):
            in_kt = True
        elif re.match(r"\.(text|data|kdata)\b", l):
            in_kt = False
        elif in_kt and re.match(r"syscall\b", l):
            kt_syscall = True
    if kt_syscall:
        return "print/exit syscalls inside a .ktext handler are exceptions for the handler on QEMU (harness limitation, see README)"
    if any(re.match(r"mtc0\s+\$\w+,\s*\$15,\s*1", l) for l in code):
        return "EBase relocation: the harness owns the exception vector at 0x80000180 (a relocated vector is not supported)"
    return None


def list_tests(only=None):
    names = sorted(f[:-4] for f in os.listdir(TESTDIR) if f.endswith(".asm"))
    if only:
        bad = [o for o in only if o not in names]
        if bad:
            sys.stderr.write("oracle.py: no such test: %s\n" % ", ".join(bad))
            sys.exit(2)
        names = [n for n in names if n in only]
    return names


def run_one(env, name, path=None):
    if path is None:
        path = os.path.join(ASMDIR, name[4:] + ".asm") if name.startswith("asm/") else os.path.join(TESTDIR, name + ".asm")
    src = open(path).read()
    if name.startswith("asm/"):
        src += "\n" + "\n".join("# oracle: " + x for x in ASM_DIRECTIVES.get(name[4:], [])) + "\n"
    d = Directives.parse(src)
    res = {"name": name, "verdict": "FAIL", "details": [], "model_term": None, "qemu_term": None}
    tdir = tempfile.mkdtemp(prefix="o_" + name.replace("/", "_") + "_", dir=env.work)
    try:
        model = run_model(env, path, d.max_steps or 100000, d.bare)
        mrec = model_record(model)
        res["model_term"] = mrec["term"]
        res["executed"] = model.get("executed", [])
        qrec = qemu_record(env, model, tdir)
        res["qemu_term"] = qrec["term"]
        res["verdict"], res["details"] = judge(model, mrec, qrec, d)
        res["directives"] = d.raw
    except HarnessError as e:
        res["verdict"], res["details"] = "FAIL", ["harness: " + str(e)]
    except subprocess.TimeoutExpired as e:
        res["verdict"], res["details"] = "FAIL", ["timeout: " + str(e)]
    return res


INSTR_LEAN = os.path.join(ROOT, "Semantics", "Instruction.lean")


def instruction_constructors():
    """Every constructor name of `inductive Instruction`, parsed from the Lean source (never hardcoded)."""
    names, inside = [], False
    for ln in open(INSTR_LEAN).read().splitlines():
        if re.match(r"^inductive Instruction\b", ln):
            inside = True
            continue
        if inside:
            if ln and not ln[0].isspace():
                break
            m = re.match(r"^\s+\|\s*(\w+)\b", ln)
            if m:
                names.append(m.group(1))
    return names


def coverage_check(results):
    """Behaviour coverage: every `Instruction` constructor must have been EXECUTED by the model (`MipsRun
    --coverage`: `step` reached `execute` on that decoded instruction) in at least one `tests/oracle/*.asm`
    program, i.e. in a program that is also run on QEMU.  Returns (executed, total, missing)."""
    ctors = instruction_constructors()
    seen = set()
    for r in results:
        if not r["name"].startswith("asm/"):
            seen.update(r.get("executed", []))
    missing = [c for c in ctors if c not in seen]
    return len(ctors) - len(missing), len(ctors), missing


def cmd_run(env, args):
    names = list_tests(args.only)
    if not names:
        sys.stderr.write("oracle.py: no tests found in %s\n" % TESTDIR)
        return 2
    skipped = []
    if args.asm:
        for f in sorted(os.listdir(ASMDIR)):
            if not f.endswith(".asm"):
                continue
            why = asm_unsupported(os.path.join(ASMDIR, f))
            if why:
                skipped.append(("asm/" + f[:-4], why))
            else:
                names.append("asm/" + f[:-4])
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        results = list(ex.map(lambda n: run_one(env, n), names))
    rc = report(results, args, skipped)
    if not args.only:     # full runs only: a filtered run cannot cover everything
        done, total, missing = coverage_check(results)
        print("COVERAGE: %d/%d Instruction constructors executed by tests/oracle programs" % (done, total))
        if missing:
            print("COVERAGE FAIL: never executed by any oracle program: " + " ".join(missing))
            rc = 1
    return rc


def report(results, args, skipped=()):
    cnt = {"PASS": 0, "DEVIATION": 0, "FAIL": 0, "KNOWN_BUG": 0}
    for r in results:
        cnt[r["verdict"]] += 1
        v = {"DEVIATION": "DEVIATION(declared)", "KNOWN_BUG": "KNOWN-MODEL-BUG"}.get(r["verdict"], r["verdict"])
        print("%-20s %s  [model %s | qemu %s]" % (v, r["name"], r["model_term"], r["qemu_term"]))
        if r["verdict"] != "PASS" or args.verbose:
            for ln in r["details"][:40]:
                print("      " + ln)
            if len(r["details"]) > 40:
                print("      ... %d more" % (len(r["details"]) - 40))
    for n, why in skipped:
        print("SKIP                 %s: %s" % (n, why))
    print("SUMMARY: %d tests, %d pass, %d declared deviations, %d known model bugs, %d fail, %d skipped (unsupported by the harness)"
          % (len(results), cnt["PASS"], cnt["DEVIATION"], cnt["KNOWN_BUG"], cnt["FAIL"], len(skipped)))
    if args.json:
        json.dump({"summary": cnt, "skipped": skipped, "results": results}, open(args.json, "w"), indent=1)
    return 1 if cnt["FAIL"] else 0


def cmd_list(args):
    for n in list_tests(args.only):
        d = Directives.parse(open(os.path.join(TESTDIR, n + ".asm")).read())
        hdr = ""
        for ln in open(os.path.join(TESTDIR, n + ".asm")):
            if ln.startswith("#") and "oracle:" not in ln:
                hdr = ln.lstrip("# ").strip()
                break
        print("%-28s %s" % (n, hdr[:70]))
        for r in d.raw:
            print("      # oracle: " + r[:100])
    return 0


# ----------------------------------------------------------------------------- encodings oracle
# Known legitimate differences: (regex on the full source line, reason).  Anything else that
# differs is a mismatch.  Declared lines are reported as DECLARED, and a declaration whose line
# does NOT differ is itself a failure (stale).
ENC_DECLARED = [
    (r"^li \$t0,(0|5|65535)$",
     "our li uses `ori $rt,$zero,imm` for 0..65535 (MARS-compatible); llvm-mc uses `addiu $rt,$zero,imm`"),
    (r"^li \$t0,(65536|0x12345678|0xffff0000|0xffffffff)$",
     "32-bit li: ours is always aui+ori via $at (aui $at,$0,hi = the LUI word; MARS-compatible); llvm-mc picks lui-only / addiu forms when it can"),
    (r"^la \$t0,",
     "our la expands via $at (`aui $at,$0,hi; ori $rt,$at,lo`, MARS/SPIM style); llvm-mc: `lui $rt,%hi; addiu $rt,$rt,%lo`"),
    (r"^move ",
     "our move is `addu $rd,$zero,$rs` (MARS/SPIM); llvm-mc emits `or $rd,$rs,$zero`"),
    (r"^abs ",
     "abs expands via move: ours `addu $rd,$zero,$rs`, llvm-mc `addu $rd,$rs,$zero` (same value, bgez/sub identical)"),
]


# Forms llvm-mc 21 cannot assemble for -mcpu=mips32r6 although the manual defines them: the expected word is
# built by hand from the instruction's bit layout (mipsdoc.py insn NAME) and compared with our assembler.
ENC_MANUAL = {
    "wait 5": ([0x42000160], "MD00086 Rev 6.06 WAIT p.442: COP0 010000 | CO=1 | code(24:6)=5 | 100000"),
    # llvm-mc 21 accepts RDPGPR/WRPGPR only with microMIPS ("instruction requires a CPU feature not currently enabled").
    "rdpgpr $t0,$t1": ([0x41494000], "MD00086 Rev 6.06 RDPGPR p.335: COP0 010000 | RDPGPR 01010 | rt(20:16)=$t1 | rd(15:11)=$t0 | 0(10:0)"),
    "rdpgpr $zero,$ra": ([0x415F0000], "MD00086 Rev 6.06 RDPGPR p.335: COP0 010000 | 01010 | rt=$ra(31) | rd=$zero(0) | 0"),
    "wrpgpr $t0,$t1": ([0x41C94000], "MD00086 Rev 6.06 WRPGPR p.444: COP0 010000 | WRPGPR 01110 | rt(20:16)=$t1 | rd(15:11)=$t0 | 0(10:0)"),
    "wrpgpr $ra,$zero": ([0x41C0F800], "MD00086 Rev 6.06 WRPGPR p.444: COP0 010000 | 01110 | rt=$zero(0) | rd=$ra(31) | 0"),
    # Llvm-mc 21 has no mnemonic for the negated CMP predicates
    "cmp.or.s $f0,$f2,$f4": ([0x46841011], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn OR 10001"),
    "cmp.or.s $f31,$f30,$f29": ([0x469DF7D1], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn OR 10001"),
    "cmp.or.d $f0,$f2,$f4": ([0x46A41011], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn OR 10001"),
    "cmp.or.d $f31,$f30,$f29": ([0x46BDF7D1], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn OR 10001"),
    "cmp.une.s $f0,$f2,$f4": ([0x46841012], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn UNE 10010"),
    "cmp.une.s $f31,$f30,$f29": ([0x469DF7D2], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn UNE 10010"),
    "cmp.une.d $f0,$f2,$f4": ([0x46A41012], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn UNE 10010"),
    "cmp.une.d $f31,$f30,$f29": ([0x46BDF7D2], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn UNE 10010"),
    "cmp.ne.s $f0,$f2,$f4": ([0x46841013], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn NE 10011"),
    "cmp.ne.s $f31,$f30,$f29": ([0x469DF7D3], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn NE 10011"),
    "cmp.ne.d $f0,$f2,$f4": ([0x46A41013], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn NE 10011"),
    "cmp.ne.d $f31,$f30,$f29": ([0x46BDF7D3], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn NE 10011"),
    "cmp.sor.s $f0,$f2,$f4": ([0x46841019], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SOR 11001"),
    "cmp.sor.s $f31,$f30,$f29": ([0x469DF7D9], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SOR 11001"),
    "cmp.sor.d $f0,$f2,$f4": ([0x46A41019], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SOR 11001"),
    "cmp.sor.d $f31,$f30,$f29": ([0x46BDF7D9], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SOR 11001"),
    "cmp.sune.s $f0,$f2,$f4": ([0x4684101A], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SUNE 11010"),
    "cmp.sune.s $f31,$f30,$f29": ([0x469DF7DA], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SUNE 11010"),
    "cmp.sune.d $f0,$f2,$f4": ([0x46A4101A], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SUNE 11010"),
    "cmp.sune.d $f31,$f30,$f29": ([0x46BDF7DA], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SUNE 11010"),
    "cmp.sne.s $f0,$f2,$f4": ([0x4684101B], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SNE 11011"),
    "cmp.sne.s $f31,$f30,$f29": ([0x469DF7DB], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10100 (S) | ft | fs | fd | 0 | condn SNE 11011"),
    "cmp.sne.d $f0,$f2,$f4": ([0x46A4101B], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SNE 11011"),
    "cmp.sne.d $f31,$f30,$f29": ([0x46BDF7DB], "MD00086 Rev 6.06 CMP.condn.fmt p.136 diagram, Table A.17 p.457: COP1 010001 | 10101 (D) | ft | fs | fd | 0 | condn SNE 11011"),
}


def enc_lines():
    ls = []
    for ln in open(ENCLIST):
        ln = ln.rstrip("\n")
        if ln.strip() and not ln.startswith("#"):
            ls.append(ln.strip())
    return ls


ASM_TABLES = [("Int.lean", "intTable"), ("Memory.lean", "memoryTable"), ("Branch.lean", "branchTable"),
              ("System.lean", "systemTable"), ("Fpu.lean", "fpuTable"), ("Fpu.lean", "fmtRows"),
              ("Pseudo.lean", "idiomTable"), ("Pseudo.lean", "macroTable")]


def lean_def_body(src, name, path):
    """Body text of `def <name> ...` up to the next blank line. Exits with a clear message if the definition is
    not found, so a rename or reformatting in Semantics/Asm/ cannot silently shrink the mnemonic set."""
    m = re.search(r"(?:^|\n)def\s+" + re.escape(name) + r"\b.*?:=\s*(.*?)\n\n", src, re.S)
    if not m:
        sys.stderr.write("oracle.py: cannot find `def %s` in %s (if it was renamed or restructured, update ASM_TABLES)\n"
                         % (name, path))
        sys.exit(2)
    return m.group(1)


def asm_mnemonics():
    """Every mnemonic of the assembler tables (Semantics/Asm/*.lean): machine instructions, macros and idioms.
    Per-format rows (`("add." ++ f.sfx, ...)`) expand to both formats `.s` and `.d`."""
    ms = set()
    for fname, table in ASM_TABLES:
        path = os.path.join(ASMDIR_LEAN, fname)
        body = lean_def_body(open(path).read(), table, path)
        ms |= set(re.findall(r'\("([a-z0-9.]+)",', body))
        for base in re.findall(r'\("([a-z0-9.]+\.)" \+\+ f\.sfx', body):
            ms |= {base + "s", base + "d"}
    if len(ms) < 100:
        sys.stderr.write("oracle.py: only %d mnemonics parsed from %s (table format changed?)\n" % (len(ms), ASMDIR_LEAN))
        sys.exit(2)
    return ms


def trace_mnemonics():
    """Mnemonics of every Instruction constructor (scripts/trace.py --json): each must be in encodings.list,
    so an instruction implemented in the model but missing from the assembler tables (e.g. sb) is reported."""
    out = os.path.join(tempfile.mkdtemp(prefix="trace_"), "t.json")
    r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "trace.py"), "--out", out + ".md", "--json", out],
                       cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(out):
        sys.stderr.write("oracle.py: scripts/trace.py --json failed:\n" + r.stdout[-500:] + r.stderr[-500:])
        sys.exit(2)
    ms = set()
    for c in json.load(open(out))["constructors"]:
        ms |= set(c.get("mnemonics") or [])
    return ms


NEEDS_AT = re.compile(r"^(blt|bge|bgt|ble|bltu|bgeu|bgtu|bleu|abs|la|li)\b")


def enc_programs(lines):
    ours, theirs = [], []
    for i, ln in enumerate(lines):
        mark = "0xE5C00000+%d" % i
        body = ln.replace("@T", "T%d" % i).replace("@B", "B%d" % i)
        ours += [".align 6", ".word %s" % mark, "B%d: nop" % i, "nop", body, "nop", "T%d: nop" % i]
        pre, post = ((".set at"), (".set noat")) if NEEDS_AT.match(ln) else ("", "")
        theirs += [".align 6", ".word %s" % mark, "B%d: nop" % i, "nop"] + ([pre] if pre else []) + [body] \
            + ([post] if post else []) + ["nop", "T%d: nop" % i]
    ours_src = ".text\n" + "\n".join(ours) + "\n"
    theirs_src = ".set noreorder\n.set noat\n.text\n.globl _start\n_start:\n" + "\n".join(theirs) + "\n"
    return ours_src, theirs_src


def split_records(words_by_addr_or_list, n):
    """words: list of 32-bit ints from the start; returns per-record word lists via markers."""
    recs, cur = {}, None
    for w in words_by_addr_or_list:
        if 0xE5C00000 <= w < 0xE5C00000 + n:
            cur = w - 0xE5C00000
            recs[cur] = []
        elif cur is not None:
            recs[cur].append(w)
    out = {}
    for i, ws in recs.items():
        ws = ws[2:]                      # drop the two leading nops (B label region)
        while ws and ws[-1] == 0:
            ws.pop()
        out[i] = ws
    return out


def assemble_ours(env, src, tdir, tag):
    p = os.path.join(tdir, tag + ".asm")
    open(p, "w").write(src)
    r = subprocess.run([env.mipsrun, "--max-steps", "0", p], capture_output=True, text=True)
    try:
        j = json.loads(r.stdout)
    except ValueError:
        raise HarnessError("MipsRun gave no JSON: " + r.stderr[:200])
    return j


def assemble_llvm(env, src, tdir, tag):
    s = os.path.join(tdir, tag + ".s")
    open(s, "w").write(src)
    o = os.path.join(tdir, tag + ".o")
    r = subprocess.run([env.llvm_tool("llvm-mc"), MC_TRIPLE, MC_CPU,
                        "-filetype=obj", s, "-o", o], capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    e = os.path.join(tdir, tag + ".elf")
    r = subprocess.run([env.llvm_tool("ld.lld"), "-m", LD_EMU, "-Ttext=0x00400000", "-e", "_start",
                        o, "-o", e, "--no-rosegment", "-z", "norelro"], capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    b = os.path.join(tdir, tag + ".bin")
    subprocess.run([env.llvm_tool("llvm-objcopy"), "-O", "binary", "-j", ".text", e, b], check=True)
    data = open(b, "rb").read()
    words = [int.from_bytes(data[k:k + 4], BYTEORDER) for k in range(0, len(data) - len(data) % 4, 4)]
    return words, e


def objdump_words(env, words, tdir):
    """Disassemble a list of words with llvm-objdump (best effort)."""
    b = os.path.join(tdir, "dis.bin")
    open(b, "wb").write(b"".join(w.to_bytes(4, BYTEORDER) for w in words))
    r = subprocess.run([env.llvm_tool("llvm-objdump"), "-D", "-b", "binary", "--triple=mipsel-unknown-elf",
                        "--mcpu=mips32r6", b], capture_output=True, text=True)
    out = []
    for ln in r.stdout.splitlines():
        m = re.match(r"\s*[0-9a-f]+:\s+(?:[0-9a-f]{2} ){4}\s*(.*)", ln)
        if m:
            out.append(m.group(1).strip())
    return out


def cmd_encodings(env, args):
    lines_all = enc_lines()
    covered = {l.split()[0] for l in lines_all}
    manual = [l for l in lines_all if l in ENC_MANUAL]
    lines = [l for l in lines_all if l not in ENC_MANUAL]
    unc = sorted((asm_mnemonics() | trace_mnemonics()) - covered)
    tdir = tempfile.mkdtemp(prefix="enc_", dir=env.work)
    ours_src, theirs_src = enc_programs(lines)
    n = len(lines)
    # ours
    bad_ours, bad_theirs = {}, {}
    active = list(range(n))

    def try_ours(idx):
        src, _ = enc_programs([lines[i] for i in idx])
        return assemble_ours(env, src, tdir, "ours")
    j = try_ours(active)
    if not j.get("assembled"):
        # find the offending lines one by one
        keep = []
        for i in active:
            jj = try_ours([i])
            if jj.get("assembled"):
                keep.append(i)
            else:
                bad_ours[i] = jj.get("error")
        active = keep
    # theirs
    def try_theirs(idx):
        _, src = enc_programs([lines[i] for i in idx])
        return assemble_llvm(env, src, tdir, "theirs")
    words, info = try_theirs(active)
    if words is None:
        keep = []
        for i in active:
            w, inf = try_theirs([i])
            if w is None:
                bad_theirs[i] = inf.strip().splitlines()[0] if inf.strip() else "error"
            else:
                keep.append(i)
        active = keep
    # re-assemble final sets with consistent index mapping (markers are 0..len(active)-1)
    act_lines = [lines[i] for i in active]
    jo = try_ours(active)
    wt, _ = try_theirs(active)
    img = {a: w for a, w in jo["image"]}
    base = 0x00400000
    top = max(img) if img else base
    ow = [img.get(base + 4 * k, 0) for k in range((top - base) // 4 + 1)]
    ro, rt = split_records(ow, len(act_lines)), split_records(wt, len(act_lines))
    declared = [(re.compile(p), r) for p, r in ENC_DECLARED]
    used = set()
    results = []
    mism = 0
    for k, ln in enumerate(act_lines):
        a, b = ro.get(k), rt.get(k)
        if a == b:
            results.append({"line": ln, "status": "SAME", "ours": a, "llvm": b})
            continue
        dec = [i for i, (rx, _) in enumerate(declared) if rx.search(ln)]
        dis = objdump_words(env, b or [], tdir) if b else []
        res = {"line": ln, "ours": a, "llvm": b, "llvm_disasm": dis}
        if dec:
            used.add(dec[0])
            res["status"] = "DECLARED"
            res["reason"] = declared[dec[0]][1]
        else:
            res["status"] = "MISMATCH"
            mism += 1
        results.append(res)
    for i in sorted(bad_ours):
        results.append({"line": lines[i], "status": "MISMATCH", "reason": "our assembler rejects: %s" % bad_ours[i]})
        mism += 1
    for i in sorted(bad_theirs):
        results.append({"line": lines[i], "status": "MISMATCH", "reason": "llvm-mc rejects: %s" % bad_theirs[i]})
        mism += 1
    for ln in manual:
        src, _ = enc_programs([ln])
        jm = assemble_ours(env, src, tdir, "manual")
        if not jm.get("assembled"):
            results.append({"line": ln, "status": "MISMATCH", "reason": "our assembler rejects: %s" % jm.get("error")})
            mism += 1
            continue
        im = {a: w for a, w in jm["image"]}
        om = split_records([im.get(base + 4 * k, 0) for k in range((max(im) - base) // 4 + 1)], 1).get(0)
        want, why = ENC_MANUAL[ln]
        if om == want:
            results.append({"line": ln, "status": "DECLARED", "ours": om, "llvm": None,
                            "reason": "llvm-mc cannot assemble this for mips32r6; ours equals the word built from the manual: " + why})
        else:
            results.append({"line": ln, "status": "MISMATCH", "ours": om, "llvm": want,
                            "reason": "ours differs from the manual-derived word: " + why})
            mism += 1
    stale = [declared[i][0].pattern for i in range(len(declared)) if i not in used and declared[i][1] != "—"]
    for s in stale:
        results.append({"line": s, "status": "MISMATCH", "reason": "stale declaration (no difference occurred)"})
        mism += 1
    for m in unc:
        results.append({"line": m, "status": "MISMATCH", "reason": "mnemonic of the Semantics/Asm tables or the model not covered by encodings.list"})
        mism += 1
    fx = lambda ws: " ".join("%08x" % w for w in ws) if ws is not None else "-"
    for r in results:
        if r["status"] == "SAME" and not args.verbose:
            continue
        print("%-9s %-34s" % (r["status"], r["line"]), end="")
        if "ours" in r:
            print(" ours=%s llvm=%s" % (fx(r["ours"]), fx(r["llvm"])), end="")
            if r.get("llvm_disasm"):
                print("  [llvm: %s]" % " ; ".join(r["llvm_disasm"]), end="")
        if r.get("reason"):
            print("\n          reason: " + r["reason"], end="")
        print()
    cnt = {s: sum(1 for r in results if r["status"] == s) for s in ("SAME", "DECLARED", "MISMATCH")}
    print("ENCODINGS: %d forms, %d same, %d declared differences, %d mismatches"
          % (len(lines_all), cnt["SAME"], cnt["DECLARED"], cnt["MISMATCH"]))
    if args.json:
        json.dump({"summary": cnt, "results": results}, open(args.json, "w"), indent=1)
    return 1 if mism else 0


# ----------------------------------------------------------------------------- selftest
def cmd_selftest(env, args):
    ok = True

    def check(name, cond, extra=""):
        nonlocal ok
        print("%-5s selftest: %s %s" % ("ok" if cond else "FAIL", name, extra))
        ok = ok and cond

    def rec(**kw):
        base = {"gpr": [0] * 32, "fcsr": 0, "fpr": [0] * 32, "status": 0, "cause": 0,
                "epc": 0, "badvaddr": 0, "errorepc": 0, "pc": 0x400000, "output": "", "mem": {},
                "term": "exit", "kind": "exit"}
        base.update(kw)
        return base
    model = {"initial": {"cp0": {"status": CU1}}, "fcsr_mask": 0xFF83FFFF}
    D = Directives.parse
    m = rec()
    q = rec(); q["gpr"] = list(q["gpr"]); q["gpr"][8] = 5
    v, det = judge(model, m, q, D(""))
    check("undeclared mismatch fails", v == "FAIL" and any("gpr:t0" in x for x in det), v)
    v, _ = judge(model, m, q, D("# oracle: expect-deviation gpr:t0 QEMU wrong, MD00086 rev 6.06 p.1"))
    check("declared deviation is reported separately", v == "DEVIATION", v)
    v, det = judge(model, m, rec(), D("# oracle: expect-deviation gpr:t0 reason cite"))
    check("stale declared deviation fails", v == "FAIL" and any("stale" in x for x in det), v)
    v, _ = judge(model, m, q, D("# oracle: unpredictable gpr:t0 MD00086 p.1"))
    check("unpredictable field is not compared", v == "PASS", v)
    v, _ = judge(model, m, q, D("# oracle: ignore-regs t0"))
    check("ignore-regs skips a register", v == "PASS", v)
    v, det = judge(model, m, rec(), D("# oracle: expect gpr:t0=7"))
    check("wrong manual expectation on the model fails", v == "FAIL" and any("expectation" in x for x in det), v)
    v, _ = judge(model, m, rec(), D("# oracle: expect gpr:zero=0"))
    check("right manual expectation passes", v == "PASS", v)
    v, det = judge(model, m, rec(), D("# oracle: unpredictable fcsr"))
    check("citation is mandatory", v == "FAIL" and any("directive error" in x for x in det), v)
    v, det = judge(model, m, q, D("# oracle: known-model-bug gpr:t0 MD00086-Rev-6.06-p.1 model-wrong-example"))
    check("known-model-bug is reported separately and does not fail", v == "KNOWN_BUG" and any("KNOWN MODEL BUG" in x for x in det), v)
    v, det = judge(model, m, rec(), D("# oracle: known-model-bug gpr:t0 MD00086-Rev-6.06-p.1 fixed-now"))
    check("known-model-bug that stops occurring fails (remove it)", v == "FAIL" and any("stale known-model-bug" in x for x in det), v)
    v, _ = judge(model, m, q, D("# oracle: known-model-bug gpr:t0 only-two-words"))
    check("known-model-bug needs citation and description", v == "FAIL", v)
    ctors = instruction_constructors()
    check("constructor list is parsed from the Lean source", len(ctors) > 100 and "add" in ctors, len(ctors))
    d0, t0, miss = coverage_check([{"name": "x", "executed": ctors[:-1]}, {"name": "asm/y", "executed": ctors[-1:]}])
    check("coverage check names a never-executed constructor (tests/asm programs do not count)",
          miss == ctors[-1:] and d0 == t0 - 1, miss)
    check("coverage check passes when all executed", coverage_check([{"name": "x", "executed": ctors}])[2] == [], "")
    q2 = rec(status=0xFFFFFFFF ^ STATUS_MASK, cause=0x40000000)
    v, _ = judge(model, m, q2, D(""))
    check("bits outside the documented Status/Cause masks are ignored", v == "PASS", v)
    q3 = rec(term="unhandled_exception(ExcCode=8)", kind="unhandled_exception")
    v, _ = judge(model, m, q3, D(""))
    check("termination kind mismatch fails", v == "FAIL", v)
    # end-to-end: a program with a deliberately wrong manual expectation must FAIL; a right one PASS
    tdir = tempfile.mkdtemp(prefix="selftest_", dir=env.work)
    prog = "li $t0, 5\nli $v0, 10\nsyscall\n"
    for tag, hdr, want in (("good", "# oracle: expect gpr:t0=5\n", "PASS"), ("bad", "# oracle: expect gpr:t0=6\n", "FAIL")):
        p = os.path.join(tdir, tag + ".asm")
        open(p, "w").write(hdr + prog)
        r = run_one(env, "st_" + tag, p)
        check("end-to-end %s expectation -> %s" % (tag, want), r["verdict"] == want, str(r["details"][:2]))
    # QEMU really executes our image: $t0 mismatch is detected if model and QEMU differ
    p = os.path.join(tdir, "ovf.asm")
    open(p, "w").write("lui $t0,0x7fff\nori $t0,$t0,0xffff\nadd $t1,$t0,$t0\n")
    r = run_one(env, "st_ovf", p)
    check("end-to-end unhandled overflow agrees", r["verdict"] == "PASS", str(r["details"][:3]))
    # real declared deviation (QEMU SC misalignment) end to end: declared -> DEVIATION; undeclared -> FAIL;
    # a stale extra declaration -> FAIL
    src = open(os.path.join(TESTDIR, "exc_sc_misaligned.asm")).read()
    # the same program with one deviation re-declared as a known model bug (the model is the side that is wrong): KNOWN_BUG
    as_bug = src.replace("# oracle: expect-deviation gpr:t1 ", "# oracle: known-model-bug gpr:t1 ")
    if as_bug == src:
        check("exc_sc_misaligned.asm still has the line the selftest uses", False)
    variants = {"known-bug": (as_bug, "KNOWN_BUG"), "known-bug-stale": (as_bug + "# oracle: known-model-bug gpr:t5 MD00086-Rev-6.06-p.1 declared bug that does not occur\n", "FAIL"),
                "declared": (src, "DEVIATION"),
                "undeclared": ("\n".join(l for l in src.splitlines() if "expect-deviation" not in l) + "\n", "FAIL"),
                "stale": (src.replace("# oracle: expect-deviation gpr:t1", "# oracle: expect-deviation gpr:t2 stale reason\n# oracle: expect-deviation gpr:t1"), "FAIL")}
    for tag, (text, want) in variants.items():
        p = os.path.join(tdir, "dev_" + tag + ".asm")
        open(p, "w").write(text)
        r = run_one(env, "st_dev_" + tag, p)
        check("end-to-end %s directive -> %s" % (tag, want), r["verdict"] == want, r["verdict"])
    print("SELFTEST:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


# ----------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", nargs="?", default="run", choices=["run", "selftest"])
    ap.add_argument("--only", action="append", help="test name (repeatable)")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--encodings", action="store_true")
    ap.add_argument("--asm", action="store_true", help="also run the tests/asm programs (those the harness cannot run are listed as SKIP with the reason)")
    ap.add_argument("--json")
    ap.add_argument("--keep", action="store_true", help="keep build artefacts (prints the directory)")
    ap.add_argument("--timeout", type=float, default=20.0, help="QEMU wall-clock limit per test (s)")
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 2))
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()
    if args.list:
        return cmd_list(args)
    work = tempfile.mkdtemp(prefix="oracle_")
    try:
        env = Env(work, args.keep, args.timeout)
        if args.cmd == "selftest":
            return cmd_selftest(env, args)
        if args.encodings:
            return cmd_encodings(env, args)
        return cmd_run(env, args)
    finally:
        if args.keep:
            print("artefacts kept in", work)
        else:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())

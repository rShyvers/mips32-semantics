#!/usr/bin/env python3
"""Generator for the machine-generated programs of tests/oracle (FP compare/convert/flags/traps, CpU, movcf, bc1l, madd, random pools, ...).

    python3 tests/oracle/gen/gen_tests.py      # (re)writes tests/oracle/<name>.asm for every generated test

The .asm files are the committed artefacts (each carries its own manual citations and `# oracle:` directives); this script only records how
they were produced. Seeds are fixed, so the output is deterministic. Hand-written tests are not touched.
"""
import os
import struct, random, sys
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
def f32(x): return struct.unpack(">I", struct.pack(">f", x))[0]
def f64(x):
    b = struct.unpack(">Q", struct.pack(">d", x))[0]; return (b >> 32, b & 0xffffffff)
def hx(v): return "0x%08x" % (v & 0xffffffff)
RM = ["RN", "RZ", "RP", "RM"]

class T:
    def __init__(s, name, title, cites, dirs=()):
        s.name, s.title, s.cites, s.dirs = name, title, cites, list(dirs)
        s.t, s.k, s.nres, s.lab, s.datal = [], [], 0, 0, []
    def e(s, *l): s.t += l
    def slot(s):
        o = s.nres * 4; s.nres += 1; return o
    def store(s, reg, base="$s7"): s.e("sw %s, %d(%s)" % (reg, s.slot(), base))
    def lbl(s): s.lab += 1; return "L%d" % s.lab
    def single(s, fr, v): s.e("li $t9, %s" % hx(v), "mtc1 $t9, $f%d" % fr)
    def double(s, fr, hl):
        s.e("li $t9, %s" % hx(hl[1]), "mtc1 $t9, $f%d" % fr, "li $t9, %s" % hx(hl[0]), "mtc1 $t9, $f%d" % (fr + 1))
    def write(s, exit=True, resptr=True):
        o = ["# " + l for l in s.title.split("\n")] + ["# " + l for l in s.cites.split("\n")] + ["# oracle: " + d for d in s.dirs]
        o += [".data"] + s.datal + ["res: .space %d" % (s.nres * 4 + 64)]
        if s.k: o += [".ktext"] + s.k
        o += [".text"]
        if resptr: o += ["la $s7, res"]
        o += s.t
        if exit: o += ["li $v0, 10", "syscall"]
        open(os.path.join(OUT, s.name + ".asm"), "w").write("\n".join(o) + "\n")

S_NAN_Q, S_NAN_S = 0x7fc00000, 0x7fa00000
D_NAN_Q, D_NAN_S = (0x7ff80000, 0), (0x7ff40000, 0)
CONDS = ["f","un","eq","ueq","olt","ult","ole","ule","sf","ngle","seq","ngl","lt","nge","le","ngt"]

# ---------------------------------------------------------------- compare predicates
def gen_cond(fmt):
    cites = ("MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113 (Tables 3.1/3.2: 16 predicates; the signaling ones (cond bit 3) raise Invalid on ANY NaN,\n"
             "the quiet ones only on a signaling NaN); FCSR layout MD00082 Vol I-A Rev 6.01 FCSR, FCC0..7 in bits 23, 31..25.")
    t = T("fp_cond_all_" + fmt, "All 16 compare predicates x {1<2, 1=1, 2>1, (1,QNaN), (1,SNaN)} on .%s with a different cc per predicate; the whole FCSR\n"
          "(condition codes + Invalid flag/cause) after each compare is stored to memory." % fmt, cites)
    if fmt == "s":
        cases = [(f32(1.0), f32(2.0)), (f32(1.0), f32(1.0)), (f32(2.0), f32(1.0)), (f32(1.0), S_NAN_Q), (f32(1.0), S_NAN_S)]
        for a, b in cases:
            t.single(0, a); t.single(2, b)
            for i, c in enumerate(CONDS):
                t.e("ctc1 $zero, $31", "c.%s.s $fcc%d, $f0, $f2" % (c, i % 8), "cfc1 $t0, $31"); t.store("$t0")
    else:
        cases = [(f64(1.0), f64(2.0)), (f64(1.0), f64(1.0)), (f64(2.0), f64(1.0)), (f64(1.0), D_NAN_Q), (f64(1.0), D_NAN_S)]
        for a, b in cases:
            t.double(0, a); t.double(2, b)
            for i, c in enumerate(CONDS):
                t.e("ctc1 $zero, $31", "c.%s.d $fcc%d, $f0, $f2" % (c, (i * 3) % 8), "cfc1 $t0, $31"); t.store("$t0")
    t.write()

# ---------------------------------------------------------------- movf/movt etc.
def gen_movcf():
    t = T("fp_movcf", "movf/movt (GPR), movf.s/movt.s/movf.d/movt.d and movn/movz.s/.d with condition codes 0 and non-zero.\n"
          "cc0 = 1, cc3 = 0, cc5 = 1 are set by compares; a conditional move that does not move leaves the destination unchanged.",
          "MD00086 Vol II-A Rev 6.06: MOVF p.276, MOVT p.281 (GPR), MOVF.fmt p.277, MOVT.fmt p.282, MOVN.fmt p.280, MOVZ.fmt p.285; C.cond.fmt p.110.",
          ["expect gpr:s0=0xdead gpr:s1=0x11 gpr:s2=0x11 gpr:s3=0xdead gpr:s4=0x11 gpr:s5=0xdead gpr:s6=0xdead"])
    t.single(0, f32(1.0)); t.single(4, f32(2.0))
    t.e("c.lt.s $fcc0, $f0, $f4", "c.eq.s $fcc3, $f0, $f4", "c.lt.s $fcc5, $f0, $f4")
    t.e("li $t0, 0x11")
    for r in range(16, 23): t.e("li $s%d, 0xdead" % (r - 16))
    t.e("movf $s0, $t0, $fcc0", "movt $s1, $t0, $fcc0", "movf $s2, $t0, $fcc3", "movt $s3, $t0, $fcc3",
        "movt $s4, $t0, $fcc5", "movf $s5, $t0, $fcc5", "movf $s6, $t0")
    t.double(2, f64(2.0))
    for r in range(10, 26, 2):
        t.e("li $t9, 0x%04x0000" % (0xa000 + r), "mtc1 $t9, $f%d" % r, "mtc1 $t9, $f%d" % (r + 1))
    t.e("movf.s $f10, $f0, $fcc3", "movt.s $f12, $f0, $fcc3", "movt.d $f14, $f2, $fcc5", "movf.d $f16, $f2, $fcc5",
        "movf.s $f18, $f0", "movt.s $f20, $f0",
        "movn.s $f22, $f0, $t0", "movz.s $f24, $f0, $t0")
    t.e("li $t9, 0xbbbb0000", "mtc1 $t9, $f26", "mtc1 $t9, $f27", "mtc1 $t9, $f28", "mtc1 $t9, $f29")
    t.e("movz.d $f26, $f2, $zero", "movn.d $f28, $f2, $zero")
    t.write()

# ---------------------------------------------------------------- bc1fl / bc1tl
def gen_bc1l():
    t = T("fp_bc1l_cc", "bc1fl/bc1tl, taken and not taken, cc 0 and non-zero: the delay slot executes only when the branch is taken (likely form).\n"
          "cc0 = 1, cc3 = 0, cc5 = 1. Each case adds 1 to $sN in the delay slot and 100 in the skipped fall-through instruction.",
          "MD00086 Vol II-A Rev 6.06: BC1FL p.58, BC1TL p.62 (branch likely: 'the delay slot instruction is annulled when not taken').",
          ["expect gpr:s0=1 gpr:s1=100 gpr:s2=1 gpr:s3=100 gpr:s4=1 gpr:s5=100 gpr:s6=1 gpr:s7=100"])
    t.single(0, f32(1.0)); t.single(4, f32(2.0))
    t.e("c.lt.s $fcc0, $f0, $f4", "c.eq.s $fcc3, $f0, $f4", "c.lt.s $fcc5, $f0, $f4")
    for r in range(8): t.e("li $s%d, 0" % r)
    cases = [("bc1tl", "$fcc0, "), ("bc1fl", "$fcc0, "), ("bc1fl", "$fcc3, "), ("bc1tl", "$fcc3, "),
             ("bc1tl", "$fcc5, "), ("bc1fl", "$fcc5, "), ("bc1tl", ""), ("bc1fl", "")]
    for i, (m, cc) in enumerate(cases):
        l = t.lbl()
        t.e("%s %s%s" % (m, cc, l), "addiu $s%d, $s%d, 1" % (i, i), "addiu $s%d, $s%d, 100" % (i, i), "%s: nop" % l)
    t.write(resptr=False)

# ---------------------------------------------------------------- round/trunc/ceil/floor.w.d
def gen_round_d():
    t = T("fp_round_trunc_ceil_floor_w_d", "round/trunc/ceil/floor.w.d on 2.5 -2.5 1.5 -1.5 0.5 -0.5 3.7 -3.7 1e10 -1e10 +Inf QNaN 2^31 -2^31 (result word and FCSR).\n"
          "Out-of-range / NaN / Inf inputs give the invalid-operation result 0x7fffffff (legacy, Has2008=0) and Invalid; inexact results set Inexact.",
          "MD00086 Vol II-A Rev 6.06: ROUND.W.fmt p.342, TRUNC.W.fmt p.441, CEIL.W.fmt p.128, FLOOR.W.fmt p.186; MD00082 Vol I-A Rev 6.01 Table 6.3 p.82 (word fixed point: 0x7fffffff for a NaN / too-big operand).")
    vals = [2.5, -2.5, 1.5, -1.5, 0.5, -0.5, 3.7, -3.7, 1e10, -1e10, float("inf"), None, 2147483648.0, -2147483648.0]
    for v in vals:
        t.double(0, D_NAN_Q if v is None else f64(v))
        for op in ("round", "trunc", "ceil", "floor"):
            t.e("ctc1 $zero, $31", "%s.w.d $f4, $f0" % op, "mfc1 $t0, $f4", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
    t.write()

# ---------------------------------------------------------------- cvt under each RM
def gen_cvt_rm():
    t = T("fp_cvt_all_rounding_modes", "cvt.w.d / cvt.s.d / cvt.d.s / cvt.s.w / cvt.w.s under each rounding mode RN RZ RP RM (FCSR.RM = 0..3).\n"
          "Result word and FCSR (flags) after each conversion; includes overflow to Inf/max-finite, an inexact narrowing and an exact one.",
          "MD00086 Vol II-A Rev 6.06: CVT.W.fmt p.160, CVT.S.fmt p.159, CVT.D.fmt p.153, FCSR.RM MD00082 Vol I-A Rev 6.01 FCSR description (p.88-95); rounding: sec 6.7.2 p.100.")
    dvals = [2.5, -2.5, 1.5, 0.5, -0.5, 1.1, 1e10, 1e40, 1e-46, -1e40, 3.0]
    for rm in range(4):
        for v in dvals:
            t.double(0, f64(v))
            t.e("li $t8, %d" % rm, "ctc1 $t8, $31", "cvt.w.d $f4, $f0", "mfc1 $t0, $f4", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
            t.e("ctc1 $t8, $31", "cvt.s.d $f6, $f0", "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
        for v in (2.5, -0.5, 16777217.0, 3.4e38, 1.5):
            t.single(8, f32(v)) if abs(v) < 1e38 or v == 3.4e38 else None
            t.e("li $t8, %d" % rm, "ctc1 $t8, $31", "cvt.w.s $f4, $f8", "mfc1 $t0, $f4", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
        for w in (0x01000001, 0x7fffffff, 0x80000001, 5):
            t.e("li $t9, %s" % hx(w), "mtc1 $t9, $f10", "li $t8, %d" % rm, "ctc1 $t8, $31", "cvt.s.w $f12, $f10", "mfc1 $t0, $f12", "cfc1 $t1, $31")
            t.store("$t0"); t.store("$t1")
        t.single(14, f32(1.1)); t.e("li $t8, %d" % rm, "ctc1 $t8, $31", "cvt.d.s $f16, $f14", "mfc1 $t0, $f16", "mfc1 $t2, $f17", "cfc1 $t1, $31")
        t.store("$t0"); t.store("$t2"); t.store("$t1")
    t.write()

# ---------------------------------------------------------------- arithmetic flags
def gen_flags(fmt):
    cites = ("MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102 (IEEE exceptions: Invalid, Division-by-zero, Overflow, Underflow, Inexact; default results per rounding mode),\n"
             "FCSR Flags bits 6..2 (V Z O U I) and Cause bits 17..12; MD00086 Vol II-A Rev 6.06 ADD.fmt p.34, SUB.fmt p.389, MUL.fmt p.302, DIV.fmt p.170, SQRT.fmt p.382.")
    t = T("fp_flags_arith_" + fmt, "add/sub/mul/div/sqrt (.%s) in each rounding mode RN RZ RP RM: result bits and FCSR (flags + cause) for exact, inexact, overflow,\n"
          "underflow, divide-by-zero and invalid cases. Flags are cleared before every operation, enables are 0." % fmt, cites)
    if fmt == "s":
        V = dict(one=f32(1.0), two=f32(2.0), three=f32(3.0), tiny30=f32(2.0 ** -30), mx=0x7f7fffff, mn=0x00800000, half=f32(0.5),
                 inf=0x7f800000, ninf=0xff800000, zero=0, nzero=0x80000000, neg1=f32(-1.0), e30=f32(1e-30), four=f32(4.0), sixteen=f32(16.0))
        cases = [("add", "one", "tiny30"), ("add", "mx", "mx"), ("add", "inf", "ninf"), ("add", "one", "two"), ("sub", "inf", "inf"), ("sub", "one", "tiny30"),
                 ("mul", "mn", "half"), ("mul", "e30", "e30"), ("mul", "zero", "inf"), ("mul", "mx", "two"), ("mul", "three", "three"),
                 ("div", "one", "zero"), ("div", "zero", "zero"), ("div", "one", "three"), ("div", "mx", "half"), ("div", "neg1", "zero"), ("div", "inf", "inf"), ("div", "e30", "mx"),
                 ("sqrt", "neg1", None), ("sqrt", "two", None), ("sqrt", "four", None), ("sqrt", "nzero", None), ("sqrt", "inf", None), ("sqrt", "mn", None)]
    else:
        D = lambda x: f64(x)
        V = dict(one=D(1.0), two=D(2.0), three=D(3.0), tiny30=D(2.0 ** -60), mx=(0x7fefffff, 0xffffffff), mn=(0x00100000, 0), half=D(0.5),
                 inf=(0x7ff00000, 0), ninf=(0xfff00000, 0), zero=(0, 0), nzero=(0x80000000, 0), neg1=D(-1.0), e30=D(1e-200), four=D(4.0))
        cases = [("add", "one", "tiny30"), ("add", "mx", "mx"), ("add", "inf", "ninf"), ("sub", "inf", "inf"), ("mul", "mn", "half"), ("mul", "e30", "e30"),
                 ("mul", "zero", "inf"), ("div", "one", "zero"), ("div", "zero", "zero"), ("div", "one", "three"), ("div", "mx", "half"),
                 ("sqrt", "neg1", None), ("sqrt", "two", None), ("sqrt", "four", None), ("sqrt", "nzero", None)]
    for op, a, b in cases:
        if fmt == "s":
            t.single(2, V[a]);
            if b: t.single(4, V[b])
        else:
            t.double(2, V[a])
            if b: t.double(4, V[b])
        for rm in range(4):
            ins = "%s.%s $f6, $f2" % (op, fmt) + (", $f4" if b else "")
            t.e("li $t8, %d" % rm, "ctc1 $t8, $31", ins, "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
            if fmt == "d": t.e("mfc1 $t2, $f7"); t.store("$t2")
    t.write()

# ---------------------------------------------------------------- FP traps
def gen_traps():
    cites = ("MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.98-99 (an enabled exception -> Floating Point exception, ExcCode 15, destination not written, Flags not updated, Cause set);\n"
             "MD00090 Vol III Rev 6.02 Cause ExcCode 15 = FPE.")
    t = T("fp_trap_enabled_nohandler", "Enabled Divide-by-zero: div.s 1/0 with FCSR.Enables.Z set takes the FP exception (ExcCode 15) at once; the destination keeps its\n"
          "old value, there is no handler so the run ends unhandled.", cites, ["expect cause=0x3c"])
    t.single(2, f32(1.0)); t.single(4, 0); t.single(6, 0x12345678)
    t.e("li $t8, 0x400", "ctc1 $t8, $31", "div.s $f6, $f2, $f4", "li $s0, 99")
    t.write(exit=False)
    # handler version
    cites2 = cites
    t = T("fp_trap_enabled_handler", "FP exceptions with a .ktext handler: Inexact, Invalid (sqrt -1), Divide-by-zero, Overflow, Underflow (enabled one at a time), a no-trap case\n"
          "(exact add, Overflow enabled) and cvt.w.s of NaN with all enables. The handler records ExcCode history ($s6), FCSR at the trap ($s5), count ($s4),\n"
          "clears FCSR.Cause and skips the instruction. Destination registers are stored after each case; the program ends by running off the text.\n"
          "Overflow with the Overflow trap enabled: Cause = O only (no Inexact), because 'Inexact is signaled if the rounded result overflows WITHOUT an overflow trap'.",
          cites2,
          ["expect gpr:s4=6", "expect-deviation mem:0x1001002c MD00082 Vol I-A Rev 6.01 sec 6.7.2.6 p.102: Inexact is signaled on overflow only 'without an overflow trap'; with Enables.O set the model reports Cause=O (0x4200 with the enable), QEMU also sets Cause.I (0x5200)"])
    t.k = ["mfc0 $k0, $13", "srl $k0, $k0, 2", "andi $k0, $k0, 31", "sll $s6, $s6, 8", "or $s6, $s6, $k0", "addiu $s4, $s4, 1", "cfc1 $s5, $31",
           "li $k1, 0xfffc0fff", "and $k1, $s5, $k1", "ctc1 $k1, $31", "mfc0 $k0, $14", "addiu $k0, $k0, 4", "mtc0 $k0, $14", "eret"]
    t.e("li $s4, 0", "li $s6, 0")
    mx = 0x7f7fffff
    def case(enable, setup, op):
        t.e("li $t9, 0x12345678", "mtc1 $t9, $f6", "li $t8, %s" % hx(enable), "ctc1 $t8, $31")
        for fr, v in setup: t.single(fr, v)
        t.e("li $t8, %s" % hx(enable), "ctc1 $t8, $31", op, "mfc1 $t0, $f6", "cfc1 $t1, $31", "ctc1 $zero, $31"); t.store("$t0"); t.store("$t1"); t.store("$s5")
    case(0x080, [(2, f32(1.0)), (4, f32(3.0))], "div.s $f6, $f2, $f4")           # I
    case(0x800, [(2, f32(-1.0))], "sqrt.s $f6, $f2")                              # V
    case(0x400, [(2, f32(1.0)), (4, 0)], "div.s $f6, $f2, $f4")                   # Z
    case(0x200, [(2, mx), (4, mx)], "add.s $f6, $f2, $f4")                        # O
    case(0x100, [(2, f32(1e-30)), (4, f32(1e-30))], "mul.s $f6, $f2, $f4")        # U (tiny*tiny)
    case(0x200, [(2, f32(1.0)), (4, f32(2.0))], "add.s $f6, $f2, $f4")            # no trap
    case(0xf80, [(2, S_NAN_Q)], "cvt.w.s $f6, $f2")                               # V on NaN conversion
    t.write(exit=False)

# ---------------------------------------------------------------- Coprocessor Unusable
def gen_cpu():
    cites = ("MD00090 Vol III Rev 6.02 sec 6.2.22 (Coprocessor Unusable: ExcCode 11, Cause.CE = coprocessor number when Status.CU1 = 0); MD00086 Vol II-A Rev 6.06 each FP instruction's 'Exceptions: Coprocessor Unusable'.")
    t = T("exc_cpu_unusable_nohandler", "Status.CU1 cleared via mtc0, then add.s: Coprocessor Unusable (ExcCode 11, Cause.CE = 1), unhandled.", cites, ["expect cause=0x1000002c"])
    t.e("mtc0 $zero, $12", "add.s $f2, $f4, $f6")
    t.write(exit=False, resptr=False)
    t = T("exc_cpu_unusable_handler", "With CU1 = 0 every FP-unit instruction raises Coprocessor Unusable: the handler logs Cause (ExcCode 11, CE 1) per instruction and skips it.\n"
          "Covers arithmetic, loads/stores, moves to/from coprocessor, FCSR access, compare, bc1t (with its delay slot), movf (GPR), movf.s, madd.s, lwxc1, ldc1, mfhc1.\n"
          "Whether the integer movf takes the exception is per its manual page ('Exceptions: Coprocessor Unusable, Reserved Instruction').",
          cites, ["expect gpr:s4=20"])
    t.k = ["mfc0 $k0, $13", "sw $k0, 0($s7)", "addiu $s7, $s7, 4", "addiu $s4, $s4, 1", "mfc0 $k0, $14", "addiu $k0, $k0, 4", "mtc0 $k0, $14", "eret"]
    t.datal = [".align 3", "dat: .word 1, 2, 3, 4"]
    t.e("li $s4, 0", "la $t0, dat", "li $t1, 8", "mtc0 $zero, $12")
    ins = ["add.s $f2, $f4, $f6", "lwc1 $f2, 0($t0)", "swc1 $f2, 0($t0)", "mfc1 $t2, $f2", "mtc1 $t2, $f2", "cfc1 $t2, $31", "ctc1 $t2, $31",
           "c.eq.s $f2, $f4", "movf $t3, $t2, $fcc0", "movf.s $f2, $f4, $fcc0", "madd.s $f2, $f4, $f6, $f8", "lwxc1 $f2, $t1($t0)", "ldc1 $f2, 0($t0)",
           "mfhc1 $t2, $f2", "sqrt.d $f2, $f4", "cvt.d.s $f2, $f4", "ldxc1 $f2, $t1($t0)", "movn.s $f2, $f4, $t1", "mov.s $f2, $f4"]
    for i in ins: t.e(i, "addiu $s5, $s5, 1")
    l = t.lbl(); t.e("bc1t " + l, "addiu $s6, $s6, 1", l + ": nop")
    t.write(exit=False)   # runs off the end

def gen_nanprop():
    cites = ("MD00082 Vol I-A Rev 6.01 sec 6.3.1.4 p.81 ('An SNaN is never produced as a result value'), sec 6.3.1.5 p.82 ('a QNaN operand causes an arithmetic operation to supply a QNaN result. "
             "When possible, this QNaN result is one of the operand QNaN values'; Table 6.3: new QNaN 0x7fbfffff when none can be copied), sec 6.7.2.1 p.100.\n"
             "NOTE legacy encoding (Has2008 = 0): fraction MSB (bit 22) = 1 is SIGNALING, 0 is QUIET, so 0x7fc00001 is an sNaN and 0x7fa00003 a QNaN.")
    t = T("fp_nan_propagation_signaling", "add/sub/mul/div.s with legacy-signaling NaN operands (0x7fc00001, 0xffc00005): Invalid is raised and the result is the default QNaN 0x7fbfffff.", cites, [])
    Q1, Q2, S1 = 0x7fc00001, 0x7fc00002, 0x7fa00003    # Q1,Q2: signaling (legacy); S1: quiet
    for op in ("add", "sub", "mul", "div"):
        for a, b in [(f32(1.0), Q1), (Q1, f32(1.0)), (Q1, Q2), (0xffc00005, f32(2.0))]:
            t.single(2, a); t.single(4, b)
            t.e("ctc1 $zero, $31", "%s.s $f6, $f2, $f4" % op, "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
    t.write()
    dirs = []
    t = T("fp_nan_propagation_quiet", "add/sub/mul/div.s with QUIET NaN operands (0x7fa00003 = QNaN, 0x7fa00004 = QNaN, 0x7fc00001 = sNaN): no Invalid for a QNaN with a number; the result is a NaN and never\n"
          "a signaling one (compared: isNaN, bit 22, FCSR). The exact payload is a documented pin: the model returns the first quiet-NaN operand unchanged ('when possible ... one of the operand QNaN values'),\n"
          "QEMU returns the default QNaN 0x7fbfffff. With exactly one QNaN operand (and a number) the operand QNaN is mandatory, so those slots are 'expect-deviation' (+ 'expect');\n"
          "with two NaN operands which one is returned is not specified, so those raw word slots stay 'unpredictable'.",
          cites, dirs)
    QA, QB = 0x7fa00003, 0x7fa00004
    cases = [(f32(1.0), QA), (QA, f32(1.0)), (QA, QB), (QB, QA), (QA, Q1), (Q1, QA)]
    for op in ("add", "sub", "mul", "div"):
        for ci, (a, b) in enumerate(cases):
            t.single(2, a); t.single(4, b)
            t.e("ctc1 $zero, $31", "%s.s $f6, $f2, $f4" % op, "mfc1 $t0, $f6", "cfc1 $t1, $31")
            raw = t.slot() * 0 + (t.nres - 1) * 4
            t.e("sw $t0, %d($s7)" % raw)
            t.e("sll $t2, $t0, 1", "lui $t3, 0xff00", "sltu $t2, $t3, $t2", "srl $t4, $t0, 22", "andi $t4, $t4, 1", "sll $t2, $t2, 1", "or $t2, $t2, $t4"); t.store("$t2"); t.store("$t1")
            addr = 0x10010000 + raw
            if ci in (0, 1):
                dirs.append("expect-deviation mem:0x%08x MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: \"When possible, this QNaN result is one of the operand QNaN values\" (exactly one QNaN operand, the other a number: the operand QNaN is mandatory); QEMU returns the default QNaN 0x7fbfffff" % addr)
                dirs.append("expect mem:0x%08x=0x%08x" % (addr, QA))
            else:
                dirs.append("unpredictable mem:0x%08x MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified" % addr)
    dirs.append("unpredictable gpr:t0 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: raw NaN payload of the last result (see mem slots)")
    dirs.append("unpredictable fpr:f6 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: raw NaN payload of the last result")
    t.dirs[:] = dirs
    t.write()

# ---------------------------------------------------------------- madd family
def gen_madd():
    cites = ("MD00086 Vol II-A Rev 6.06: MADD.fmt p.256 ('The intermediate product is rounded ...; the results and flags are as if separate multiply and add instructions were executed'),\n"
             "MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310.")
    t = T("fp_madd_msub_nmadd_nmsub", "madd/msub/nmadd/nmsub .s and .d: a plain case and a case where a fused operation would differ from multiply-then-add (the product rounds);\n"
          "result bits and FCSR after each, in RN and RZ.", cites)
    a = f32(1.0 + 2.0 ** -12); c = f32(-(1.0 + 2.0 ** -11))
    for rm in (0, 1, 2, 3):
        for (x, y, z) in ((f32(2.0), f32(3.0), f32(4.0)), (a, a, c)):
            t.single(2, x); t.single(4, y); t.single(6, z)
            for op in ("madd", "msub", "nmadd", "nmsub"):
                t.e("li $t8, %d" % rm, "ctc1 $t8, $31", "%s.s $f8, $f6, $f2, $f4" % op, "mfc1 $t0, $f8", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
        da = f64(1.0 + 2.0 ** -27); dc = f64(-(1.0 + 2.0 ** -26))
        for (x, y, z) in ((f64(2.0), f64(3.0), f64(4.0)), (da, da, dc)):
            t.double(2, x); t.double(4, y); t.double(6, z)
            for op in ("madd", "msub", "nmadd", "nmsub"):
                t.e("li $t8, %d" % rm, "ctc1 $t8, $31", "%s.d $f8, $f6, $f2, $f4" % op, "mfc1 $t0, $f8", "mfc1 $t2, $f9", "cfc1 $t1, $31")
                t.store("$t0"); t.store("$t2"); t.store("$t1")
    t.write()

# ---------------------------------------------------------------- recip / rsqrt
def gen_recip():
    cites = ("MD00086 Vol II-A Rev 6.06: RECIP.fmt p.336 / RSQRT.fmt p.343: 'The numeric accuracy of this operation is implementation dependent ... differs from the exact result by no more than one ULP'.")
    t = T("fp_recip_rsqrt_exact", "recip/rsqrt .s/.d on operands where the exact result is representable (powers of two, +-0, Inf); result bits and FCSR.", cites)
    for fmt in "sd":
        for v in (1.0, 2.0, 4.0, 0.5, -2.0, 0.0, float("inf"), 0.25, 16.0, -1.0):
            if fmt == "s": t.single(2, f32(v))
            else: t.double(2, f64(v))
            for op in ("recip", "rsqrt"):
                if op == "rsqrt" and v in (2.0, 0.5, -2.0, 16.0 * 0 - 1) and False: continue
                t.e("ctc1 $zero, $31", "%s.%s $f6, $f2" % (op, fmt), "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
                if fmt == "d": t.e("mfc1 $t2, $f7"); t.store("$t2")
    t.write()
    t = T("fp_recip_rsqrt_inexact", "recip/rsqrt of 3.0 / 2.0 / 10.0 (.s and .d): the result is an approximation with implementation-dependent accuracy (<= 1 ULP), so the\n"
          "result bits and the Inexact flag are not compared; the program checks only that both executors terminate the same way.", cites,
          ["unpredictable fpr MD00086 Rev 6.06 RECIP.fmt p.336 / RSQRT.fmt: numeric accuracy implementation dependent (within 1 ULP)",
           "unpredictable gpr MD00086 Rev 6.06 RECIP.fmt p.336: accuracy and rounding-mode dependence implementation dependent (results stored in GPRs)",
           "unpredictable fcsr MD00086 Rev 6.06 RECIP.fmt p.336: Inexact/Underflow flags of an approximation are implementation dependent",
           "unpredictable mem MD00086 Rev 6.06 RECIP.fmt p.336: stored approximation results"])
    for fmt in "sd":
        for v in (3.0, 2.0, 10.0):
            if fmt == "s": t.single(2, f32(v))
            else: t.double(2, f64(v))
            for op in ("recip", "rsqrt"):
                t.e("ctc1 $zero, $31", "%s.%s $f6, $f2" % (op, fmt), "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
    t.write()

# ---------------------------------------------------------------- indexed ld/st
def gen_indexed():
    t = T("fp_indexed_ldst", "lwxc1/ldxc1/swxc1/sdxc1: address = base + index register; word and doubleword (8-byte aligned).",
          "MD00086 Vol II-A Rev 6.06: LWXC1 p.254, LDXC1 p.218, SWXC1 p.406, SDXC1 p.364 (MIPS32 Release 2).",
          ["expect fpr:f2=0x11223344 fpr:f4=0x55667788"])
    t.datal = [".align 3", "src: .word 0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00", "dst: .space 32"]
    t.e("la $t0, src", "li $t1, 0", "li $t2, 4", "li $t3, 8", "lwxc1 $f2, $t1($t0)", "lwxc1 $f3, $t2($t0)", "ldxc1 $f4, $t1($t0)", "ldxc1 $f6, $t3($t0)",
        "la $t4, dst", "li $t5, 4", "li $t6, 8", "swxc1 $f2, $zero($t4)", "swxc1 $f3, $t5($t4)", "sdxc1 $f6, $t6($t4)", "li $t7, 16", "sdxc1 $f4, $t7($t4)",
        "lw $s0, 0($t4)", "lw $s1, 4($t4)", "lw $s2, 8($t4)", "lw $s3, 12($t4)", "lw $s4, 16($t4)", "lw $s5, 20($t4)")
    t.write()

def gen_hc1():
    t = T("fp_mfhc1_mthc1", "mfhc1/mthc1 with Status.FR = 0 on an even register: the 64-bit view of FPR[fs] is the even/odd pair, so mfhc1 reads the odd register of\n"
          "the pair and mthc1 writes it. (An odd fs is UNPREDICTABLE with FR=0 and is not used.)",
          "MD00086 Vol II-A Rev 6.06: MFHC1 p.271 ('GPR[rt] <- FPR[fs]63..32 ... UNPREDICTABLE if Status.FR = 0 and fs is odd'), MTHC1 p.295.",
          ["expect gpr:s0=0xaabbccdd gpr:s1=0x11223344 fpr:f5=0x01020304 fpr:f4=0x11223344"])
    t.e("li $t0, 0x11223344", "li $t1, 0xaabbccdd", "mtc1 $t0, $f2", "mthc1 $t1, $f2", "mfhc1 $s0, $f2", "mfc1 $s1, $f2", "mfc1 $s2, $f3",
        "li $t2, 0x01020304", "mtc1 $t0, $f4", "mthc1 $t2, $f4", "mfhc1 $s3, $f4")
    t.write()

def gen_pref():
    t = T("pref_prefx_nop", "pref with every hint 0..31 and prefx, at valid, unmapped (0) and misaligned addresses, never raise an exception and change no state.",
          "MD00086 Vol II-A Rev 6.06: PREF p.321 ('...it is not an exception if the address is invalid / PREF does not take TLB or address-error exceptions'), PREFX p.329.",
          ["expect gpr:s0=7"])
    t.datal = ["d: .word 1, 2"]
    t.e("la $t0, d", "li $t1, 4", "li $s0, 7")
    for h in range(32): t.e("pref %d, 0($t0)" % h)
    t.e("pref 0, 1($t0)", "pref 4, 0($zero)", "pref 1, -1($zero)", "prefx 0, $t1($t0)", "prefx 31, $zero($zero)", "prefx 5, $t1($t1)", "lw $s1, 0($t0)")
    t.write()

def gen_diei():
    t = T("di_ei_status", "di/ei: the old Status is returned in rt, Status.IE is cleared/set; di/ei with rt = $zero; Status read back.",
          "MD00086 Vol II-A Rev 6.06: DI p.164, EI p.176 (MIPS32 Release 2); Status.IE MD00090 Vol III Rev 6.02.",
          ["expect gpr:s0=0x20000000 gpr:s1=0x20000001 gpr:s2=0x20000001 gpr:s3=0x20000000 gpr:s4=0 gpr:s5=1"])
    t.e("ei $s0", "di $s1", "ei $zero", "mfc0 $s2, $12", "di", "mfc0 $s3, $12", "ei $s6", "di $zero", "mfc0 $s4, $12", "andi $s4, $s4, 1", "ei", "mfc0 $s5, $12", "andi $s5, $s5, 1")
    t.write(resptr=False)

def gen_scaddr():
    t = T("ll_sc_address_mismatch", "sc to an address different from the preceding ll fails (rt = 0, memory unchanged); a matching sc succeeds (rt = 1).",
          "MD00086 Vol II-A Rev 6.06 SC p.347: 'An SC will fail if the aligned address of the SC does not match that of the preceding LL.'",
          ["expect gpr:t1=0 gpr:t3=1 gpr:s0=0x10 gpr:s1=0x20"])
    t.datal = ["a: .word 0x10", "b: .word 0x20"]
    t.e("la $t4, a", "la $t5, b", "ll $t0, 0($t4)", "li $t1, 0x99", "sc $t1, 0($t5)", "ll $t0, 0($t4)", "li $t3, 0x77", "sc $t3, 0($t4)", "lw $s0, 0($t5)", "li $s1, 0x20", "lw $s2, 0($t4)")
    # s0 = b (unchanged 0x20 expected)
    t.dirs[-1] = "expect gpr:t1=0 gpr:t3=1 gpr:s0=0x20 gpr:s2=0x77"
    t.write(resptr=False)

def gen_codes():
    t = T("exc_codes_handler", "break/syscall/teq/tne/tge/tlt with non-zero code fields: the exception is taken as usual; the handler logs Cause and the faulting instruction word\n"
          "(loaded from EPC, so the encoded code field is observed) and skips it.",
          "MD00086 Vol II-A Rev 6.06: BREAK p.109 (code 20 bits), SYSCALL p.415, TEQ p.416 (code 10 bits).")
    t.k = ["mfc0 $k0, $13", "sw $k0, 0($s7)", "mfc0 $k0, $14", "lw $k1, 0($k0)", "sw $k1, 4($s7)", "addiu $s7, $s7, 8", "addiu $k0, $k0, 4", "mtc0 $k0, $14", "eret"]
    t.e("break 5", "break 1023, 1023", "break 5, 7", "li $v0, 0", "syscall 0x1234", "syscall 0xfffff", "li $t0, 3", "teq $t0, $t0, 7", "tge $t0, $t0, 1023", "tne $t0, $zero, 11",
        "tlt $zero, $t0, 5", "tgeu $t0, $t0, 3", "tltu $zero, $t0, 4", "teq $t0, $zero, 9", "sync 4", "li $s0, 1")
    t.write(exit=False)

def gen_ident():
    t = T("cp0_ident_ebase", "mfc0 PRId/Config/Config1/EBase and cfc1 FIR: implementation-specific constants are NOT compared; only fields the manual fixes are:\n"
          "Config.BE (bit 15) = 1, Config.AT = 0 (MIPS32), Config.AR = 1 (Release 2), Config1.FP (bit 0) = 1, FIR.F64 (bit 22) = 0 with FIR.S/D (bits 16,17) = 1,\n"
          "EBase bits 31..30 = 10, CPUNum (9..0) = 0 and EBase read/write round trip (restored before exit).",
          "MD00090 Vol III Rev 6.02: PRId p.221, EBase Table 9.58 p.224, Config Table 9.64 p.233-234, Config1 p.237; MD00082 Vol I-A Rev 6.01 FIR Table 6.5 p.88.",
          ["unpredictable gpr:s0 MD00090 Vol III Rev 6.02 PRId: Company/Processor ID/Revision are implementation-defined constants",
           "unpredictable gpr:s1 MD00090 Vol III Rev 6.02 Config: only BE/AT/AR are fixed by the architecture (checked in s2); the rest is implementation-defined",
           "unpredictable gpr:s3 MD00090 Vol III Rev 6.02 Config1: cache/TLB geometry fields are implementation-defined (FP bit checked in s4)",
           "unpredictable gpr:s5 MD00082 Vol I-A Rev 6.01 FIR: ProcessorID/Revision are implementation-defined (fixed bits checked in s6)"])
    t.e("mfc0 $s0, $15", "mfc0 $s1, $16", "srl $s2, $s1, 10", "andi $s2, $s2, 0x3f",   # AR(12:10) AT(14:13) BE(15) -> 6 bits = BE AT AT AR AR AR
        "mfc0 $s3, $16, 1", "andi $s4, $s3, 1", "cfc1 $s5, $0", "li $t0, 0x00070000", "and $s6, $s5, $t0",
        "mfc0 $t1, $15, 1", "srl $s7, $t1, 30", "andi $t2, $t1, 0x3ff",
        "li $t3, 0x3ffff000", "mtc0 $t3, $15, 1", "mfc0 $t4, $15, 1", "li $t5, 0x80000000", "mtc0 $t5, $15, 1", "mfc0 $t6, $15, 1")
    t.write(resptr=False)

def gen_fcsr_regs():
    t = T("fp_fcsr_aliases_reserved", "ctc1/cfc1 on FCSR ($31), FCCR ($25), FEXR ($26), FENR ($28) and FIR ($0): reserved FCSR bits (22..18) read as zero, the aliases are views of FCSR,\n"
          "writes through FCCR/FEXR/FENR touch only their fields. Values are stored after each step (enables are kept clear so no trap is taken).",
          "MD00082 Vol I-A Rev 6.01 FIR/FCCR/FEXR/FENR/FCSR register layouts (p.88-95); MD00086 Vol II-A Rev 6.06 CTC1 p.151 / CFC1 p.129-130.")
    for v in (0xffffff7f & 0xfffff07f, 0x0083f07f & 0xffffff7f, 0x00000003, 0x01000000, 0xfe800000, 0x0003f000 & 0, 0x0000007c):
        t.e("li $t0, %s" % hx(v), "ctc1 $t0, $31", "cfc1 $t1, $31", "cfc1 $t2, $25", "cfc1 $t3, $26", "cfc1 $t4, $28")
        for r in ("$t1", "$t2", "$t3", "$t4"): t.store(r)
    for reg, v in ((25, 0xff), (25, 0x0a), (26, 0x0003007c), (26, 0), (28, 0x00000f83 & 0xfffff07f | 0x0f80 & 0), (28, 0x4)):
        t.e("ctc1 $zero, $31", "li $t0, %s" % hx(v), "ctc1 $t0, $%d" % reg, "cfc1 $t1, $31", "cfc1 $t2, $25", "cfc1 $t3, $26", "cfc1 $t4, $28")
        for r in ("$t1", "$t2", "$t3", "$t4"): t.store(r)
    t.e("cfc1 $t5, $0")
    t.write()
    t.name = "fp_fcsr_aliases_reserved"
    t = T("fp_fcsr_write_traps", "Moving a value into FCSR with an enabled Cause bit takes the Floating Point exception at the ctc1 itself (ExcCode 15, FCSR keeps the written value).",
          "MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99: 'A floating point trap is generated any time both a Cause bit and its corresponding Enable bit are set. This occurs either during the execution of a floating point operation or by moving a value into the FCSR.'",
          ["expect cause=0x3c"])
    t.e("li $t0, 0x00011800", "ctc1 $t0, $31", "li $s0, 5")   # Cause.V (bit 16)... plus Enable.V (bit 11)
    t.write(exit=False, resptr=False)

def gen_fs():
    t = T("fp_flush_to_zero_fs", "FCSR.FS = 1: tiny non-zero results are flushed to zero of the same sign with Underflow+Inexact; subnormal inputs are replaced by zero (Release 5+, implementation-dependent before).",
          "MD00082 Vol I-A Rev 6.01 sec 6.7.2.4 p.101-102 ('Every tiny non-zero result is replaced with zero of the same sign ... Flushing of tiny non-zero results causes Inexact and Underflow').",
          ["expect-deviation gpr:t1 MD00082 Vol I-A Rev 6.01 6.7.2.4 p.102: flushing a tiny result raises Underflow and Inexact; QEMU 24Kf leaves the flags clear", "expect-deviation fcsr same"]
          + ["expect-deviation mem:0x%08x same" % (0x10010000 + 4 * (2 * i + 1)) for i in range(8)])
    t.single(2, f32(1e-30)); t.single(4, f32(1e-30)); t.single(8, 0x00800000); t.single(10, f32(0.5))
    for rm in range(4):
        t.e("li $t8, %s" % hx(0x01000000 | rm), "ctc1 $t8, $31", "mul.s $f6, $f2, $f4", "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
        t.e("li $t8, %s" % hx(0x01000000 | rm), "ctc1 $t8, $31", "mul.s $f6, $f8, $f10", "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
    t.write()

def gen_idx_exc():
    for nm, ins, off in (("lwxc1", "lwxc1 $f2, $t1($t0)", 1), ("swxc1", "swxc1 $f2, $t1($t0)", 2), ("ldxc1", "ldxc1 $f2, $t1($t0)", 4), ("sdxc1", "sdxc1 $f2, $t1($t0)", 2)):
        cite = "%s: the manual requires Address Error for a misaligned effective address (%s p.%s); QEMU 24Kf performs the access without an exception" % (ins.split()[0].upper(), ins.split()[0].upper(), {"lwxc1": "254", "swxc1": "406", "ldxc1": "218", "sdxc1": "364"}[ins.split()[0]])
        fields = ["term", "gpr:s0", "epc", "badvaddr", "pc", "cause"] + (["fpr:f2"] if ins[0] == "l" else ["mem:0x10010000"])
        if nm == "ldxc1": fields.append("fpr:f3")
        if nm == "sdxc1": fields.append("mem:0x10010004")
        t = T("exc_%s_misaligned" % nm, "%s at base + %d (data segment is 8-byte aligned): Address Error, EPC/BadVAddr/Cause compared; unhandled.\n"
              "(Doubleword indexed accesses at a word-aligned but not doubleword-aligned address: see the manual page, the model treats ldc1/sdc1 as word-aligned only.)" % (ins.split()[0], off),
              "MD00086 Vol II-A Rev 6.06: LWXC1 p.254, SWXC1 p.406, LDXC1 p.218, SDXC1 p.364 (Restrictions: 'An Address Error exception occurs if EffectiveAddress1..0 != 0 (not word-aligned)' / 'EffectiveAddress2..0 != 0 (not doubleword-aligned)').",
              ["expect-deviation %s %s" % (f, cite) for f in fields])
        t.datal = [".align 3", "d: .word 1, 2, 3, 4"]
        t.e("la $t0, d", "li $t1, %d" % off, ins, "li $s0, 7")
        t.write(exit=False, resptr=False)


POOL_S = [0, 0x80000000, 0x3f800000, 0xbf800000, 0x40000000, 0x40400000, 0x3dcccccd, 0x00000001, 0x007fffff, 0x00800000, 0x00800001, 0x80000001,
          0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x3f000000, 0x4b000000, 0x4b7fffff, 0x33800000, 0x34000000, 0x7e800000, 0x01000000]
POOL_D = [(0,0),(0x80000000,0),(0x3ff00000,0),(0xbff00000,0),(0x40000000,0),(0x3fb99999,0x9999999a),(0,1),(0x000fffff,0xffffffff),(0x00100000,0),(0x00100000,1),
          (0x7fefffff,0xffffffff),(0x7ff00000,0),(0xfff00000,0),(0x3fe00000,0),(0x43400000,0),(0x3ca00000,0),(0x7fd00000,0),(0x00200000,0)]
def rnd_s(r):
    k = r.random()
    if k < .5: return r.choice(POOL_S)
    if k < .8: return r.getrandbits(32) & 0xff7fffff | (r.randrange(1, 254) << 23) & 0x7f800000 if False else ((r.getrandbits(1) << 31) | (r.randrange(1, 254) << 23) | r.getrandbits(23))
    return (r.getrandbits(1) << 31) | (r.randrange(0, 255) << 23) | r.getrandbits(23) if False else ((r.getrandbits(1) << 31) | (r.randrange(100, 160) << 23) | r.getrandbits(23))
def rnd_d(r):
    k = r.random()
    if k < .5: return r.choice(POOL_D)
    e = r.randrange(1, 2046) if k < .7 else r.randrange(1000, 1050)
    m = r.getrandbits(52)
    return (((r.getrandbits(1) << 31) | (e << 20) | (m >> 32)), m & 0xffffffff)
def is_nan_s(v): return (v & 0x7fffffff) > 0x7f800000
def is_nan_d(v): return ((v[0] & 0x7fffffff) << 32 | v[1]) > 0x7ff0000000000000
def gen_rand(name, fmt, ops, seed, n):
    r = random.Random(seed)
    t = T(name, "Randomised (seeded %d) %s on .%s over edge-value pools and random normals, in all four rounding modes: result bits + FCSR. No NaN operands (payload choice is unspecified)." % (seed, "/".join(ops), fmt),
          "MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102, Table 6.14 p.100 (IEEE default results, flags, rounding modes); MD00086 Vol II-A Rev 6.06 ADD/SUB/MUL/DIV/SQRT.fmt, CVT/ROUND/TRUNC/CEIL/FLOOR.", [])
    ld = (lambda fr, v: t.single(fr, v)) if fmt == "s" else (lambda fr, v: t.double(fr, v))
    gen = rnd_s if fmt == "s" else rnd_d
    nan = is_nan_s if fmt == "s" else is_nan_d
    for i in range(n):
        op = ops[i % len(ops)]
        a = gen(r)
        while nan(a): a = gen(r)
        b = gen(r)
        while nan(b): b = gen(r)
        ld(2, a); ld(4, b)
        if op.endswith(('madd','msub')):
            c = gen(r)
            while nan(c): c = gen(r)
            ld(8, c)
        rm = r.randrange(4)
        for rm in range(4):
            if op in ("add", "sub", "mul", "div"): ins = "%s.%s $f6, $f2, $f4" % (op, fmt)
            elif op in ("sqrt",): ins = "sqrt.%s $f6, $f2" % fmt
            elif op.startswith("cvtw"): ins = "cvt.w.%s $f6, $f2" % fmt
            elif op.startswith("cvtsd"): ins = "cvt.s.d $f6, $f2"
            elif op.startswith("rnd"): ins = "%s.w.%s $f6, $f2" % (op[3:], fmt)
            elif op.startswith("madd"): ins = "%s.%s $f6, $f8, $f2, $f4" % (op, fmt)
            t.e("li $t8, %d" % rm, "ctc1 $t8, $31", ins, "mfc1 $t0, $f6", "cfc1 $t1, $31"); t.store("$t0"); t.store("$t1")
            if fmt == "d" and not op.startswith(("cvtw", "rnd")): t.e("mfc1 $t2, $f7"); t.store("$t2")
    t.write()
def gen_cmp_rand(name, fmt, seed, n):
    r = random.Random(seed)
    t = T(name, "Randomised (seeded %d) compare of .%s operands including NaNs (quiet and signaling) and edge values: all 16 predicates, the FCSR (condition code + Invalid) stored after each." % (seed, fmt),
          "MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113; MD00082 Vol I-A Rev 6.01 Table 6.2 (legacy NaN encodings).", [])
    if fmt == "s":
        pool = POOL_S + [0x7fc00000, 0x7fa00000, 0xffc00001, 0x7fbfffff, 0x7f800001]
        ld = lambda fr, v: t.single(fr, v)
    else:
        pool = POOL_D + [(0x7ff80000, 0), (0x7ff40000, 0), (0xfff80001, 5), (0x7ff7ffff, 0xffffffff), (0x7ff00000, 1)]
        ld = lambda fr, v: t.double(fr, v)
    for i in range(n):
        a, b = r.choice(pool), r.choice(pool)
        if r.random() < 0.3: b = a
        ld(0, a); ld(2, b)
        for j, c in enumerate(CONDS):
            t.e("ctc1 $zero, $31", "c.%s.%s $fcc%d, $f0, $f2" % (c, fmt, (i + j) % 8), "cfc1 $t0, $31"); t.store("$t0")
    t.write()

def gen_status_writes():
    t = T("mtc0_status_bits", "Single-bit writes to Status: IE, EXL(1), IM7..0, BEV(22), CU1(29) and combinations; each read back (masked to the implemented bits 0x2040ff07) and stored.\n"
          "Status is restored before exit (BEV/EXL redirect or mask the exit exception). ERL is not written: with ERL = 1 useg is unmapped on a real CPU/QEMU (the harness's TLB-mapped text would vanish).",
          "MD00090 Vol III Rev 6.02 Status register field descriptions (p.189 ff.: CU1 bit 29, BEV bit 22, IM bits 15..8, ERL bit 2, EXL bit 1, IE bit 0).", [])
    vals = [1 << b for b in (0, 8, 9, 10, 11, 12, 13, 14, 15, 22, 29)] + [0x0000ff00, 0x20000000 | 0xff00, 0, 0x20000001]
    t.e("li $t5, 0x2040ff07")
    for v in vals:
        t.e("li $t0, %s" % hx(v), "mtc0 $t0, $12", "mfc0 $t1, $12", "and $t1, $t1, $t5"); t.store("$t1")
    # BEV, then restore
    for v in (0x00400000 | 0x20000000, 0x00000002 | 0x20000000):
        t.e("li $t0, %s" % hx(v), "mtc0 $t0, $12", "mfc0 $t1, $12", "and $t1, $t1, $t5"); t.store("$t1")
    t.e("li $t0, 0x20000000", "mtc0 $t0, $12")
    t.write()

def gen_fir_write():
    t = T("fp_ctc1_fir_readonly", "ctc1 to FIR ($0) is ignored (FIR is read-only); cfc1 FIR before/after; cvt.d.w exact; PRId (mtc0 $15) write is ignored.",
          "MD00082 Vol I-A Rev 6.01 FIR description p.88 (read-only); MD00090 Vol III Rev 6.02 PRId p.221 (read-only).", [])
    t.e("cfc1 $s0, $0", "li $t0, 0xffffffff", "ctc1 $t0, $0", "cfc1 $t7, $0", "subu $s1, $t7, $s0", "mfc0 $s2, $15", "mtc0 $t0, $15", "mfc0 $t6, $15", "subu $s3, $t6, $s2")
    t.e("li $t9, 0x7fffffff", "mtc1 $t9, $f2", "cvt.d.w $f4, $f2", "mfc1 $t1, $f4", "mfc1 $t2, $f5"); t.store("$t1"); t.store("$t2")
    t.e("li $t9, 0x80000000", "mtc1 $t9, $f2", "cvt.d.w $f4, $f2", "mfc1 $t1, $f4", "mfc1 $t2, $f5"); t.store("$t1"); t.store("$t2")
    t.dirs += ["expect gpr:s1=0 gpr:s3=0", "unpredictable gpr:s0 MD00082 Vol I-A Rev 6.01 FIR: ProcessorID/Revision and the F64/L capability bits are implementation-defined (QEMU 24Kf: F64=1, the model: a 32-bit FPU)",
               "unpredictable gpr:t7 same as s0", "unpredictable gpr:s2 MD00090 Vol III Rev 6.02 PRId: implementation-defined constant", "unpredictable gpr:t6 same as s2"]
    t.write()


def gen_delay():
    t = T("exc_fp_cpu_in_delay_slot_handler", "An FP exception (enabled Divide-by-zero, ExcCode 15) and Coprocessor Unusable (CU1 = 0, ExcCode 11, CE 1) raised by an instruction in a branch delay slot:\n"
          "Cause.BD = 1 and EPC = the address of the branch. The handler logs Cause/EPC/FCSR and resumes after the delay slot (EPC + 8).",
          "MD00090 Vol III Rev 6.02 sec 6.2 Table 6.11 p.87 (value stored in EPC for an exception in a branch delay slot = the branch address, Cause.BD = 1); MD00082 Vol I-A Rev 6.01 6.7.1; MD00090 6.2.22.", ["expect gpr:s4=2"])
    t.k = ["mfc0 $k0, $13", "sw $k0, 0($s7)", "mfc0 $k1, $14", "sw $k1, 4($s7)", "mfc0 $k0, $12", "lui $t9, 0x2000", "or $k0, $k0, $t9", "mtc0 $k0, $12", "cfc1 $k0, $31", "sw $k0, 8($s7)", "addiu $s7, $s7, 12", "addiu $s4, $s4, 1",
           "li $k0, 0xfffc0fff", "cfc1 $t9, $31", "and $k0, $k0, $t9", "ctc1 $k0, $31", "addiu $k1, $k1, 8", "mtc0 $k1, $14", "eret"]
    t.single(2, f32(1.0)); t.single(4, 0)
    t.e("li $s4, 0", "li $t8, 0x400", "ctc1 $t8, $31", "beq $zero, $zero, A", "div.s $f6, $f2, $f4", "nop", "A: nop",
        "mtc0 $zero, $12", "beq $zero, $zero, B", "add.s $f6, $f2, $f4", "nop", "B: nop")
    t.write(exit=False)


def main():
    gen_cond("s"); gen_cond("d"); gen_movcf(); gen_bc1l(); gen_round_d(); gen_cvt_rm(); gen_flags("s"); gen_flags("d"); gen_traps(); gen_cpu()
    gen_nanprop(); gen_fcsr_regs(); gen_fs(); gen_idx_exc(); gen_madd(); gen_recip(); gen_indexed(); gen_hc1(); gen_pref(); gen_diei(); gen_scaddr(); gen_codes(); gen_ident()
    gen_status_writes(); gen_fir_write(); gen_delay()
    for k in range(2):
        gen_rand("fp_rand_s_arith_%d" % k, "s", ["add", "sub", "mul", "div", "sqrt"], 100 + k, 40)
        gen_rand("fp_rand_d_arith_%d" % k, "d", ["add", "sub", "mul", "div", "sqrt"], 200 + k, 40)
        gen_rand("fp_rand_s_cvt_%d" % k, "s", ["cvtw", "rndround", "rndtrunc", "rndceil", "rndfloor"], 300 + k, 40)
        gen_cmp_rand("fp_rand_s_compare_%d" % k, "s", 700 + k, 12)
        gen_cmp_rand("fp_rand_d_compare_%d" % k, "d", 800 + k, 12)
        gen_rand("fp_rand_s_madd_%d" % k, "s", ["madd", "msub", "nmadd", "nmsub"], 500 + k, 32)
        gen_rand("fp_rand_d_madd_%d" % k, "d", ["madd", "msub", "nmadd", "nmsub"], 600 + k, 32)
        gen_rand("fp_rand_d_cvt_%d" % k, "d", ["cvtw", "cvtsd", "rndround", "rndtrunc", "rndceil", "rndfloor"], 400 + k, 48)


if __name__ == "__main__":
    main()

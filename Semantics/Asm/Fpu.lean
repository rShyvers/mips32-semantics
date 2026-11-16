import Semantics.Asm.Operands

/-!
# Asm.Fpu — Coprocessor 1 (FPU)

GPR/FPR moves (`mfc1`/`mtc1`/`mfhc1`/`mthc1 rt, fs`), control moves (`cfc1`/`ctc1 rt, fs` with
`fs` the control register number written `$31`, `31` or the older `$f31`), the FP loads/stores
(`ft, offset(base)`), and per format `S`/`D`: arithmetic `fd, fs, ft`, unary operations and
conversions `fd, fs`. Release 6 removed C.cond.fmt, BC1F/BC1T(L), MOVF/MOVT(.fmt), MOVN/MOVZ.fmt,
the indexed loads/stores, PREFX and the MADD family; those mnemonics are not in the table.
-/

-- W6: the Release 6 FP instructions (CMP.cond.fmt, BC1EQZ/BC1NEZ, SEL/MADDF/MIN/MAX/... .fmt)
-- get their rows here when the model has their constructors.

namespace Asm

/-- An FPU control register operand: `$N`/`N`, or the `$fN` spelling. -/
def fpCtl (c : Ctx) (t : String) : Except AsmError W32 :=
  match parseFpRegister t c.line with
  | .ok n => pure (fld n)
  | .error _ => do pure (fld (← parseCopRegister "FPU control" t c.line))

/-- `rt, fs` with the second operand parsed by `src`. -/
def gprCop (src : Ctx → String → Except AsmError W32) (mk : (rt fs : W32) → Instruction) : Enc :=
  fun c ops =>
    match ops with
    | [t, s] => do pure (mk (← gpr c t) (← src c s))
    | _ => badShape c "rt, fs"

/-- `fd, fs, ft`. -/
def fp3 (mk : (fd fs ft : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, s, t] => do pure (mk (← fpr c d) (← fpr c s) (← fpr c t))
  | _ => badShape c "fd, fs, ft"

/-- `fd, fs`. -/
def fp2 (mk : (fd fs : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, s] => do pure (mk (← fpr c d) (← fpr c s))
  | _ => badShape c "fd, fs"

/-- The per-format operations, for one format suffix (`s` or `d`). -/
structure FmtOps where
  sfx : String
  add : W32 → W32 → W32 → Instruction
  sub : W32 → W32 → W32 → Instruction
  mul : W32 → W32 → W32 → Instruction
  div : W32 → W32 → W32 → Instruction
  sqrt : W32 → W32 → Instruction
  abs : W32 → W32 → Instruction
  mov : W32 → W32 → Instruction
  neg : W32 → W32 → Instruction
  recip : W32 → W32 → Instruction
  rsqrt : W32 → W32 → Instruction
  roundW : W32 → W32 → Instruction
  truncW : W32 → W32 → Instruction
  ceilW : W32 → W32 → Instruction
  floorW : W32 → W32 → Instruction
  cvtW : W32 → W32 → Instruction

/-- The table rows of one format. -/
def fmtRows (f : FmtOps) : EncTable :=
  [ ("add." ++ f.sfx, fp3 f.add), ("sub." ++ f.sfx, fp3 f.sub),
    ("mul." ++ f.sfx, fp3 f.mul), ("div." ++ f.sfx, fp3 f.div),
    ("sqrt." ++ f.sfx, fp2 f.sqrt), ("abs." ++ f.sfx, fp2 f.abs),
    ("mov." ++ f.sfx, fp2 f.mov), ("neg." ++ f.sfx, fp2 f.neg),
    ("recip." ++ f.sfx, fp2 f.recip), ("rsqrt." ++ f.sfx, fp2 f.rsqrt),
    ("round.w." ++ f.sfx, fp2 f.roundW), ("trunc.w." ++ f.sfx, fp2 f.truncW),
    ("ceil.w." ++ f.sfx, fp2 f.ceilW), ("floor.w." ++ f.sfx, fp2 f.floorW),
    ("cvt.w." ++ f.sfx, fp2 f.cvtW) ]

/-- Format S. -/
def opsS : FmtOps :=
  { sfx := "s", add := .addS, sub := .subS, mul := .mulS, div := .divS, sqrt := .sqrtS,
    abs := .absS, mov := .movS, neg := .negS, recip := .recipS, rsqrt := .rsqrtS,
    roundW := .roundWS, truncW := .truncWS, ceilW := .ceilWS, floorW := .floorWS, cvtW := .cvtWS }

/-- Format D. -/
def opsD : FmtOps :=
  { sfx := "d", add := .addD, sub := .subD, mul := .mulD, div := .divD, sqrt := .sqrtD,
    abs := .absD, mov := .movD, neg := .negD, recip := .recipD, rsqrt := .rsqrtD,
    roundW := .roundWD, truncW := .truncWD, ceilW := .ceilWD, floorW := .floorWD, cvtW := .cvtWD }

-- BEGIN R6-5
/-- The longword (L) conversions (MD00086 Vol II-A Rev 6.06: CVT.L.fmt p.154, ROUND.L.fmt p.341,
TRUNC.L.fmt p.440, CEIL.L.fmt p.127, FLOOR.L.fmt p.185, CVT.S.fmt p.159, CVT.D.fmt p.153). -/
def longRows : EncTable :=
  [ ("cvt.l.s", fp2 .cvtLS), ("cvt.l.d", fp2 .cvtLD),
    ("round.l.s", fp2 .roundLS), ("round.l.d", fp2 .roundLD),
    ("trunc.l.s", fp2 .truncLS), ("trunc.l.d", fp2 .truncLD),
    ("ceil.l.s", fp2 .ceilLS), ("ceil.l.d", fp2 .ceilLD),
    ("floor.l.s", fp2 .floorLS), ("floor.l.d", fp2 .floorLD),
    ("cvt.s.l", fp2 .cvtSL), ("cvt.d.l", fp2 .cvtDL) ]
-- END R6-5

/-- The FPU instructions. -/
def fpuTable : EncTable :=
  [ ("mfc1",  gprCop fpr .mfc1),
    ("mtc1",  gprCop fpr .mtc1),
    ("mfhc1", gprCop fpr .mfhc1),
    ("mthc1", gprCop fpr .mthc1),
    ("cfc1",  gprCop fpCtl .cfc1),
    ("ctc1",  gprCop fpCtl .ctc1),
    ("lwc1",  memOp 16 fpr .lwc1),
    ("swc1",  memOp 16 fpr .swc1),
    ("ldc1",  memOp 16 fpr .ldc1),
    ("sdc1",  memOp 16 fpr .sdc1),
    ("cvt.d.s", fp2 .cvtDS),
    ("cvt.s.d", fp2 .cvtSD),
    ("cvt.s.w", fp2 .cvtSW),
    ("cvt.d.w", fp2 .cvtDW) ] ++ fmtRows opsS ++ fmtRows opsD ++ longRows


end Asm

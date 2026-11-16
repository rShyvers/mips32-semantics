import Semantics.Asm.Operands

/-!
# Asm.Fpu — Coprocessor 1 (FPU)

GPR/FPR moves (`mfc1`/`mtc1`/`mfhc1`/`mthc1 rt, fs`), control moves (`cfc1`/`ctc1 rt, fs` with
`fs` the control register number written `$31`, `31` or the older `$f31`), the FP loads/stores
(`ft, offset(base)`), and per format `S`/`D`: arithmetic `fd, fs, ft`, unary operations and
conversions `fd, fs`. Release 6 removed C.cond.fmt, BC1F/BC1T(L), MOVF/MOVT(.fmt), MOVN/MOVZ.fmt,
the indexed loads/stores, PREFX and the MADD family; those mnemonics are not in the table.
-/

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

/-- One FP format for the assembler: its mnemonic suffix and the model's constructors of that format
(`Cop1Fmt`, the same record the decoder's per-format table `decodeCop1Fmt` uses). -/
structure FmtOps where
  sfx : String
  ops : Cop1Fmt

/-- The table rows of one format: `<op>.<sfx>` for every per-format operation (MD00086 Vol II-A
Rev 6.06: the arithmetic, unary and conversion pages of each `.fmt` instruction; CVT.L.fmt p.154,
ROUND.L.fmt p.341, TRUNC.L.fmt p.440, CEIL.L.fmt p.127, FLOOR.L.fmt p.185; SEL.fmt p.368,
SELEQZ.fmt/SELNEZ.fmt p.371, MADDF.fmt/MSUBF.fmt p.259, MAX/MIN/MAXA/MINA.fmt p.262, CLASS.fmt
p.132, RINT.fmt p.337; CVT.S.fmt p.159 and CVT.D.fmt p.153 for the format that has them). -/
def fmtRows (f : FmtOps) : EncTable :=
  let o := f.ops
  let n (m : String) : String := m ++ "." ++ f.sfx
  [ (n "add", fp3 o.add), (n "sub", fp3 o.sub), (n "mul", fp3 o.mul), (n "div", fp3 o.div),
    (n "sqrt", fp2 o.sqrt), (n "abs", fp2 o.abs), (n "mov", fp2 o.mov), (n "neg", fp2 o.neg),
    (n "recip", fp2 o.recip), (n "rsqrt", fp2 o.rsqrt),
    (n "round.w", fp2 o.roundW), (n "trunc.w", fp2 o.truncW), (n "ceil.w", fp2 o.ceilW),
    (n "floor.w", fp2 o.floorW), (n "cvt.w", fp2 o.cvtW),
    (n "round.l", fp2 o.roundL), (n "trunc.l", fp2 o.truncL), (n "ceil.l", fp2 o.ceilL),
    (n "floor.l", fp2 o.floorL), (n "cvt.l", fp2 o.cvtL),
    (n "sel", fp3 o.sel), (n "seleqz", fp3 o.seleqz), (n "selnez", fp3 o.selnez),
    (n "maddf", fp3 o.maddf), (n "msubf", fp3 o.msubf),
    (n "max", fp3 o.max), (n "min", fp3 o.min), (n "maxa", fp3 o.maxa), (n "mina", fp3 o.mina),
    (n "class", fp2 o.cls), (n "rint", fp2 o.rint) ] ++
  (o.cvtS.toList.map fun mk => (n "cvt.s", fp2 mk)) ++
  (o.cvtD.toList.map fun mk => (n "cvt.d", fp2 mk))

/-- Format S. -/
def opsS : FmtOps := { sfx := "s", ops := decodeFmtS }

/-- Format D. -/
def opsD : FmtOps := { sfx := "d", ops := decodeFmtD }

/-- The conversions from W and L (CVT.S.fmt p.159, CVT.D.fmt p.153). -/
def fromIntRows : EncTable :=
  [ ("cvt.s.w", fp2 .cvtSW), ("cvt.d.w", fp2 .cvtDW),
    ("cvt.s.l", fp2 .cvtSL), ("cvt.d.l", fp2 .cvtDL) ]

/-- `ft, target` (BC1EQZ, BC1NEZ): an FPR and a 16-bit branch offset, as `brRs`. -/
def brFt (mk : (ft off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [t, l] => do pure (mk (← fpr c t) (← branchOff c l))
  | _ => badShape c "ft, target"

/-- The `condn` names of CMP.condn.fmt and their values (MD00086 Vol II-A Rev 6.06, Table A.17,
p.457; the mnemonics `cmp.<condn>.s`/`.d` as llvm-mc prints them; `or`, `une`, `ne`, `sor`, `sune`,
`sne` from Table A.17, which llvm-mc 21 does not assemble). -/
def cmpCondnNames : List (String × Nat) :=
  [("af", 0), ("un", 1), ("eq", 2), ("ueq", 3), ("lt", 4), ("ult", 5), ("le", 6), ("ule", 7),
   ("saf", 8), ("sun", 9), ("seq", 10), ("sueq", 11), ("slt", 12), ("sult", 13), ("sle", 14),
   ("sule", 15), ("or", 17), ("une", 18), ("ne", 19), ("sor", 25), ("sune", 26), ("sne", 27)]

/-- `cmp.<condn>.s` and `cmp.<condn>.d fd, fs, ft` for every `condn` (CMP.condn.fmt, p.136). -/
def cmpRows : EncTable :=
  cmpCondnNames.flatMap fun (n, k) =>
    [("cmp." ++ n ++ ".s", fp3 (.cmpS (BitVec.ofNat 32 k))),
     ("cmp." ++ n ++ ".d", fp3 (.cmpD (BitVec.ofNat 32 k)))]

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
    ("bc1eqz", brFt .bc1eqz),   -- BC1EQZ BC1NEZ, p.54
    ("bc1nez", brFt .bc1nez) ] ++ fmtRows opsS ++ fmtRows opsD ++ fromIntRows ++ cmpRows


end Asm

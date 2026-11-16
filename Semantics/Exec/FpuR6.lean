import Semantics.Exec.Base

/-!
# Exec.FpuR6 — the Release 6 FPU instructions

The execution of the FP instructions Release 6 introduced (MD00086 Vol II-A Rev 6.06): `CMP.condn.fmt`
(p.136-140), `BC1EQZ`/`BC1NEZ` (p.54-55), `SEL.fmt` (p.368), `SELEQZ.fmt`/`SELNEZ.fmt` (p.371),
`MADDF.fmt`/`MSUBF.fmt` (p.259-260), `MAX`/`MIN`/`MAXA`/`MINA.fmt` (p.262-265), `CLASS.fmt` (p.132-133)
and `RINT.fmt` (p.337-338) (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm
is the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot;
coprocessor usable); `none` for every instruction of another family.

* The arithmetic ones (`CMP`, `MADDF`/`MSUBF`, `MAX`/`MIN`/`MAXA`/`MINA`, `RINT`) complete through
  `fpFinishS`/`fpFinishD` (FCSR Cause, the trap, Flags), on the IEEE core of `Mips.Fp`.
* `SEL`, `SELEQZ`, `SELNEZ` "do not cause data-dependent exceptions ... the FCSRCause and FCSRFlags
  fields are not modified" (p.368, p.371), and `CLASS` has "No data-dependent exceptions" and no
  FCSR update in its Operation (p.132): a plain store, FCSR untouched.
* A 32-bit result (fmt = S) goes to the low half of `FPR[fd]` (`writeFpReg`; the upper half is
  UNPREDICTABLE, MD00082 Vol I-A Rev 6.01 §6.6.2, p.98; the model keeps it, `Manual.Oracle.fprUpper`).
* `BC1EQZ`/`BC1NEZ` are branches with a delay slot, as `BEQ` (`Exec/Branch.lean`): the condition is
  bit 0 of the low word of `FPR[ft]` (`ValueFPR(ft, UNINTERPRETED_WORD)`, p.55).
-/

/-- The all-ones / all-zeros mask of `CMP.condn.S` from the predicate value (p.136: "true is all 1s
and false is all 0s, repeated the operand width of fmt"), with the flags. -/
def cmpMaskS (r : Bool × Mips.Fp.Flags) : W32 × Mips.Fp.Flags :=
  (if r.1 then BitVec.allOnes 32 else 0#32, r.2)

/-- As `cmpMaskS`, for `CMP.condn.D` (64 bits). -/
def cmpMaskD (r : Bool × Mips.Fp.Flags) : BitVec 64 × Mips.Fp.Flags :=
  (if r.1 then BitVec.allOnes 64 else 0#64, r.2)

/-- An operand of CMP.condn.S as compared: a subnormal flushed to zero of the same sign when
`FCSR.FS = 1` ("As of Release 5, every input subnormal value is replaced with zero of the same sign";
"For floating-point comparisons, the Inexact exception is not signaled when subnormal input operands
are flushed", MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102), with no flag. -/
def cmpInS (fl : Bool) (x : W32) : W32 := BitVec.ofNat 32 (Mips.Fp.binary32.flushIn fl x.toNat)

/-- As `cmpInS`, for CMP.condn.D. -/
def cmpInD (fl : Bool) (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (Mips.Fp.binary64.flushIn fl x.toNat)

/-- The `condn` field of CMP.condn.fmt (bits 4..0). -/
def cmpCondn (cond : W32) : BitVec 5 := cond.setWidth 5

/-- The effect of the Release 6 FPU instructions; `none` for every other instruction. -/
def execFpuR6 (s : State) : Instruction → Option State
  -- CMP.condn.fmt: the mask of the predicate (`Mips.Fp.f32Cmp`/`f64Cmp`) on the flushed operands,
  -- Invalid per p.140.
  | .cmpS c fd fs ft => some <| fpFinishS s fd
      (cmpMaskS (Mips.Fp.f32Cmp (cmpCondn c) (cmpInS (fpEnv s).flush (readFpReg s (regIdx fs)))
        (cmpInS (fpEnv s).flush (readFpReg s (regIdx ft)))))
  | .cmpD c fd fs ft => some <| fpFinishD s fd
      (cmpMaskD (Mips.Fp.f64Cmp (cmpCondn c) (cmpInD (fpEnv s).flush (readFpD s fs))
        (cmpInD (fpEnv s).flush (readFpD s ft))))
  -- BC1EQZ/BC1NEZ: `cond ← tmp & 1 = 0` / `≠ 0`; `target ← PC + 4 + sign_extend(offset << 2)`, as BEQ.
  | .bc1eqz ft off => some <|
    let pcNext := s.pc + 4#32
    if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 off <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bc1nez ft off => some <|
    let pcNext := s.pc + 4#32
    if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 off <<< 2)) }
  -- SEL.fmt: `FPR[fd].bit0 ? FPR[ft] : FPR[fs]`.
  | .selS fd fs ft => some <| mkNext s (writeFpReg s (regIdx fd)
      (if (readFpReg s (regIdx fd)).getLsbD 0 then readFpReg s (regIdx ft) else readFpReg s (regIdx fs)))
  | .selD fd fs ft => some <| mkNext s (writeFpD s fd
      (if (readFpReg s (regIdx fd)).getLsbD 0 then readFpD s ft else readFpD s fs))
  -- SELEQZ.fmt: `FPR[ft].bit0 ? 0 : FPR[fs]`; SELNEZ.fmt: `FPR[ft].bit0 ? FPR[fs] : 0`.
  | .seleqzS fd fs ft => some <| mkNext s (writeFpReg s (regIdx fd)
      (if (readFpReg s (regIdx ft)).getLsbD 0 then 0#32 else readFpReg s (regIdx fs)))
  | .seleqzD fd fs ft => some <| mkNext s (writeFpD s fd
      (if (readFpReg s (regIdx ft)).getLsbD 0 then 0#64 else readFpD s fs))
  | .selnezS fd fs ft => some <| mkNext s (writeFpReg s (regIdx fd)
      (if (readFpReg s (regIdx ft)).getLsbD 0 then readFpReg s (regIdx fs) else 0#32))
  | .selnezD fd fs ft => some <| mkNext s (writeFpD s fd
      (if (readFpReg s (regIdx ft)).getLsbD 0 then readFpD s fs else 0#64))
  -- MADDF/MSUBF.fmt: `FPR[fd] ± FPR[fs] × FPR[ft]` with one rounding.
  | .maddfS fd fs ft => some <| fpFinishS s fd (Mips.Fp.f32Fma (fpEnv s) false
      (readFpReg s (regIdx fd)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .maddfD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64Fma (fpEnv s) false
      (readFpD s fd) (readFpD s fs) (readFpD s ft))
  | .msubfS fd fs ft => some <| fpFinishS s fd (Mips.Fp.f32Fma (fpEnv s) true
      (readFpReg s (regIdx fd)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .msubfD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64Fma (fpEnv s) true
      (readFpD s fd) (readFpD s fs) (readFpD s ft))
  -- MAX/MIN/MAXA/MINA.fmt: one core, `Mips.Fp.f32MinMax`/`f64MinMax`, keyed by the operation.
  | .maxS fd fs ft => some <| fpFinishS s fd
      (Mips.Fp.f32MinMax .max (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .maxD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64MinMax .max (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .minS fd fs ft => some <| fpFinishS s fd
      (Mips.Fp.f32MinMax .min (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .minD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64MinMax .min (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .maxaS fd fs ft => some <| fpFinishS s fd
      (Mips.Fp.f32MinMax .maxa (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .maxaD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64MinMax .maxa (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .minaS fd fs ft => some <| fpFinishS s fd
      (Mips.Fp.f32MinMax .mina (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .minaD fd fs ft => some <| fpFinishD s fd (Mips.Fp.f64MinMax .mina (fpEnv s) (readFpD s fs) (readFpD s ft))
  -- CLASS.fmt: the class mask; no FCSR update.
  | .classS fd fs => some <| mkNext s (writeFpReg s (regIdx fd) (Mips.Fp.f32Class (readFpReg s (regIdx fs))))
  | .classD fd fs => some <| mkNext s (writeFpD s fd (Mips.Fp.f64Class (readFpD s fs)))
  -- RINT.fmt: round to an integral value per FCSR.RM.
  | .rintS fd fs => some <| fpFinishS s fd (Mips.Fp.f32Rint (fpEnv s) (readFpReg s (regIdx fs)))
  | .rintD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Rint (fpEnv s) (readFpD s fs))
  | _ => none

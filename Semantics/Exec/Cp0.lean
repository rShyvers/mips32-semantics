import Semantics.Exec.Base

/-!
# Exec.Cp0 — the coprocessor 0 moves (MFC0, MTC0, DI, EI, RDPGPR, WRPGPR)

The execution of the coprocessor 0 moves (MFC0, MTC0, DI, EI, RDPGPR, WRPGPR) (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the coprocessor 0 moves (MFC0, MTC0, DI, EI, RDPGPR, WRPGPR); `none` for every other instruction. -/
def execCp0 (s : State) : Instruction → Option State
  -- Coprocessor 0 register moves, for the `(rd, sel)` pairs of
  -- `isModeledCp0Reg`: (7,0) HWREna, (8,0) BadVAddr, (9,0) Count, (11,0) Compare,
  -- (12,0) Status, (12,1) IntCtl (`intCtlValue`), (12,2) SRSCtl (`srsCtlValue`), (13,0) Cause (read with the timer bits, `causeValue`), (14,0)
  -- EPC, (15,0) PRId, (15,1) EBase, (16,0) Config, (16,1) Config1, (16,2) Config2,
  -- (16,3) Config3, (30,0) ErrorEPC. `decode` only produces `mfc0`/`mtc0` for these; an
  -- `Instruction` value built by hand with any other pair raises Reserved
  -- Instruction, matching what the undecodable word would do. Outside Kernel
  -- Mode with `Status.CU0 = 0` they raise Coprocessor Unusable before reaching
  -- this arm (`execInstr`, `usesCop0`).
  | .mfc0 rt rd sel => some <|
    match rd.toNat, sel.toNat with
    | 7, 0 => mkNext s (writeReg s (regIdx rt) s.cp0HWREna)
    | 8, 0 => mkNext s (writeReg s (regIdx rt) s.cp0BadVAddr)
    | 9, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Count)
    | 11, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Compare)
    | 12, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Status)
    | 12, 1 => mkNext s (writeReg s (regIdx rt) intCtlValue)
    | 12, 2 => mkNext s (writeReg s (regIdx rt) srsCtlValue)
    | 13, 0 => mkNext s (writeReg s (regIdx rt) (causeValue s))
    | 14, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Epc)
    | 15, 0 => mkNext s (writeReg s (regIdx rt) prIdValue)
    | 15, 1 => mkNext s (writeReg s (regIdx rt) (ebaseValue s))
    | 16, 0 => mkNext s (writeReg s (regIdx rt) (configValue s))
    | 16, 1 => mkNext s (writeReg s (regIdx rt) config1Value)
    | 16, 2 => mkNext s (writeReg s (regIdx rt) config2Value)
    | 16, 3 => mkNext s (writeReg s (regIdx rt) config3Value)
    | 30, 0 => mkNext s (writeReg s (regIdx rt) s.cp0ErrorEpc)
    | _, _ => takeException s excCodeRI
  -- `mtc0` write masks: `BadVAddr`, `PRId`, `Config1`, `Config2` (its only R/W fields `TU`/`SU`
  -- are not implemented: "read as zero and be ignored on write", Table 9.66, p.241-242) and
  -- `Config3` ("All fields in the Config3 register are read-only", §9.48, p.245) are
  -- read-only (the write is ignored); `IntCtl` has no writable field (`VS` "is ignored on write
  -- and reads as zero" without VI/EIC, MD00090 Vol III Rev 6.02 Table 9.48, p.201); `SRSCtl`'s
  -- writable fields `ESS`/`PSS` can only hold 0 with `HSS = 0` (a larger value is UNDEFINED,
  -- Table 9.49, p.203-204; pin: the write is ignored, so they read 0); `HWREna` keeps bits 3..0 (`hwrenaWriteMask`); `Count` is
  -- fully writable ("can be written for functional or diagnostic purposes", MD00090 Vol III
  -- Rev 6.02 §9.27, p.183); a write to `Compare` stores the value and clears the timer interrupt
  -- (`Cause.TI`; §9.30, p.187); `Config` takes only `K23` (30..28), `KU` (27..25) and `K0`
  -- (2..0); `Status` keeps only `statusWriteMask`
  -- bits (others read as zero); `Cause` changes only `causeWriteMask` bits
  -- (DC, IV, IP1..0), keeping `BD`/`CE`/`ExcCode`/everything else; `EPC`/
  -- `ErrorEPC` are fully writable; `EBase` takes the Exception Base field
  -- (bits 29..12) only.
  | .mtc0 rt rd sel => some <|
    match rd.toNat, sel.toNat with
    | 7, 0 => mkNext s { s with cp0HWREna := readReg s (regIdx rt) &&& hwrenaWriteMask }
    | 8, 0 => mkNext s s
    | 9, 0 => mkNext s { s with cp0Count := readReg s (regIdx rt) }
    | 11, 0 => mkNext s { s with cp0Compare := readReg s (regIdx rt), cp0TimerInt := false }
    | 12, 0 => mkNext s { s with cp0Status := readReg s (regIdx rt) &&& statusWriteMask }
    | 12, 1 => mkNext s s
    | 12, 2 => mkNext s s
    | 13, 0 => mkNext s { s with cp0Cause :=
              (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdx rt) &&& causeWriteMask) }
    | 14, 0 => mkNext s { s with cp0Epc := readReg s (regIdx rt) }
    | 15, 0 => mkNext s s
    | 15, 1 => mkNext s { s with cp0EBase :=
              (readReg s (regIdx rt) &&& ebaseWriteMask) ||| ebaseFixedBits }
    | 16, 0 => mkNext s { s with cp0ConfigK0 := (readReg s (regIdx rt)).setWidth 3,
                                 cp0ConfigK23 := (readReg s (regIdx rt) >>> 28).setWidth 3,
                                 cp0ConfigKU := (readReg s (regIdx rt) >>> 25).setWidth 3 }
    | 16, 1 => mkNext s s
    | 16, 2 => mkNext s s
    | 16, 3 => mkNext s s
    | 30, 0 => mkNext s { s with cp0ErrorEpc := readReg s (regIdx rt) }
    | _, _ => takeException s excCodeRI
  -- `di`/`ei` (MD00086 Vol II-A Rev 6.06, DI p.164, EI p.176):
  -- `GPR[rt] ← Status; Status.IE ← 0` / `1`. The value written to `$rt` is
  -- the Status value *before* the change.
  | .di rt => some <|
    mkNext s (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdx rt)
      s.cp0Status)
  | .ei rt => some <|
    mkNext s (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdx rt)
      s.cp0Status)
  -- `rdpgpr rd, rt` / `wrpgpr rd, rt` (MD00086 Vol II-A Rev 6.06, RDPGPR p.335:
  -- "GPR[rd] ← SGPR[SRSCtlPSS, rt]"; WRPGPR p.444: "SGPR[SRSCtlPSS, rd] ← GPR[rt]").
  -- Only the normal GPRs exist (`SRSCtl.HSS = 0`: "only the normal GPRs are
  -- implemented", MD00090 Vol III Rev 6.02 Table 9.49, p.203), and "The normal
  -- GPRs are logically considered shadow set zero" (§7, p.103); `PSS` = `CSS` = 0
  -- (`srsCtlValue`), so `SGPR[0, r]` is `GPR[r]` and both are a register move.
  | .rdpgpr rd rt => some <| mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))
  | .wrpgpr rd rt => some <| mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))
  | _ => none

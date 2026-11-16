import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.DelaySlot

/-!
# Cp0 — coprocessor 0: `mfc0`/`mtc0`, `di`/`ei`, `eret`/`eretnc`, `wait`, `rdpgpr`/`wrpgpr`, `cache`; and `pause`

Constructors: `mfc0` `mtc0` `di` `ei` `eret` `eretnc` `wait` `rdpgpr` `wrpgpr` `cache`, and `pause`
(not a coprocessor-0 instruction; here because it enters standby like `wait`).

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MFC0 p.266; MTC0 p.290-291; DI p.164; EI p.176; ERET p.177-178; ERETNC p.179-180; WAIT p.442-443;
  RDPGPR p.335; WRPGPR p.444; CACHE p.114-119; PAUSE p.317-318.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Coprocessor 0 / traps and exceptions (real MIPS32 ISA)".

Every one of these instructions except `pause` needs coprocessor 0: outside Kernel Mode it raises
Coprocessor Unusable with `Cause.CE = 0` and does nothing else (`cp0_instruction_user_mode_unusable`,
one theorem for all ten; MD00090 Vol III Rev 6.02 §6.2.22, p.100). The per-instruction `_spec_raw`
theorems state the other case: they assume `hcp0 : cp0Usable s = true`, which is exactly Kernel
Mode (`cp0Usable_iff_kernelMode`: Release 6 has no `Status.CU0`; §3.5.3, p.23).

The CP0 register file is the layout table `cp0Layout` (`Exec/Cp0.lean`); `cp0ReadAt_eq` and
`cp0WriteAt_eq` write it out register by register, `mfc0_spec_raw`/`mtc0_spec_raw` are the steps.

## Theorems in this file (39)

  `cp0ReadAt_eq` `cp0WriteAt_eq` `mfc0_spec_layout` `mfc0_spec_raw` `mtc0_spec_layout`
  `mtc0_spec_raw` `mfc0_unimplemented_reads_zero` `mtc0_unimplemented_ignored` `mfc0_config3`
  `mfc0_config4` `mfc0_config5` `mtc0_config5` `mfc0_llAddr` `mtc0_llAddr` `mtc0_llAddr_clears`
  `mtc0_llAddr_never_sets` `cp0_scratch_round_trip` `causeWriteMask_eq` `statusWriteMask_eq`
  `di_spec_raw` `ei_spec_raw` `eret_spec_raw` `eretnc_spec_raw` `eretnc_keeps_llBit`
  `eretnc_in_delay_slot_reserved_instruction` `cache_spec_raw` `cache_noop` `eret_clears_llBit`
  `eret_in_delay_slot_reserved_instruction` `wait_spec_raw` `wait_preserves_state` `pause_spec_raw`
  `pause_llbit_clear` `rdpgpr_spec_raw` `wrpgpr_spec_raw` `cp0Usable_iff_kernelMode`
  `cp0_instruction_user_mode_unusable` `usesCop1_of_usesCop0` `hwrenaWriteMask_eq`
-/

set_option maxRecDepth 4000

/-! ## `mfc0`/`mtc0`, `di`/`ei`, `eret`/`eretnc`, `wait`, `cache`

(`pref` is in `Memory.lean`; the coprocessor-1 specifications are in the `Fpu*.lean` files.) -/

/-- **What `mfc0` reads: the CP0 register layout of the model, register by register** (the
table `cp0Layout`, `Exec/Cp0.lean`, with each register's read value `cp0Read`), written out. Every
`(rd, sel)` the table does not name reads 0: "Release 6: Reading a reserved register or a register
that is not implemented for the current core configuration returns 0" (MD00086 Vol II-A Rev 6.06,
MFC0, p.266). Proof device for `mfc0_spec_raw`. -/
theorem cp0ReadAt_eq (s : State) (rd sel : W32) :
    cp0ReadAt s rd sel =
      match rd.toNat, sel.toNat with
      | 4, 2 => s.cp0UserLocal
      | 7, 0 => s.cp0HWREna
      | 8, 0 => s.cp0BadVAddr
      | 8, 1 => s.cp0BadInstr
      | 8, 2 => s.cp0BadInstrP
      | 9, 0 => s.cp0Count
      | 11, 0 => s.cp0Compare
      | 12, 0 => s.cp0Status
      | 12, 1 => 0xE0000000#32
      | 12, 2 => 0#32
      | 13, 0 => s.cp0Cause ||| (s.hwInt.setWidth 32 <<< 10) |||
          (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32)
      | 14, 0 => s.cp0Epc
      | 15, 0 => 0x00010000#32
      | 15, 1 => (s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32
      | 16, 0 => 0x80000980#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) |||
          (s.cp0ConfigKU.setWidth 32 <<< 25) ||| s.cp0ConfigK0.setWidth 32
      | 16, 1 => 0x80000001#32
      | 16, 2 => 0x80000000#32
      | 16, 3 => 0x8C003000#32
      | 16, 4 => 0x80FC0000#32
      | 16, 5 => 0x00002010#32 ||| (if s.cp0Config5SBRI then 0x40#32 else 0#32)
      | 17, 0 => if s.llBit then 1#32 else 0#32
      | 30, 0 => s.cp0ErrorEpc
      | 31, 2 => s.cp0KScratch 0
      | 31, 3 => s.cp0KScratch 1
      | 31, 4 => s.cp0KScratch 2
      | 31, 5 => s.cp0KScratch 3
      | 31, 6 => s.cp0KScratch 4
      | 31, 7 => s.cp0KScratch 5
      | _, _ => 0#32 := by
  unfold cp0ReadAt
  generalize rd.toNat = n
  generalize sel.toNat = m
  symm
  split <;> (try subst_vars) <;> try rfl
  · show 0#32 = (match cp0Layout .r6 n m with | some r => cp0Read s r | none => 0#32)
    unfold cp0Layout
    split <;> simp_all

/-- **What `mtc0` writes: the CP0 register layout of the model with each register's field table**
(`cp0Layout`, `cp0Write`, `Exec/Cp0.lean`), written out. Every other `(rd, sel)` — a read-only
register or one the table does not name — is left unchanged: "Release 6: Writes to a register that is
reserved or not defined for the current core configuration are ignored" (MD00086 Vol II-A Rev 6.06,
MTC0, p.290). Proof device for `mtc0_spec_raw`. -/
theorem cp0WriteAt_eq (s : State) (rd sel v : W32) :
    cp0WriteAt s rd sel v =
      match rd.toNat, sel.toNat with
      | 4, 2 => { s with cp0UserLocal := v }
      | 7, 0 => { s with cp0HWREna := v &&& hwrenaWriteMask }
      | 9, 0 => { s with cp0Count := v }
      | 11, 0 => { s with cp0Compare := v, cp0TimerInt := false }
      | 12, 0 => { s with cp0Status := v &&& statusWriteMask }
      | 13, 0 =>
        { s with cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) ||| (v &&& causeWriteMask) }
      | 14, 0 => { s with cp0Epc := v }
      | 15, 1 => { s with cp0EBase := (v &&& 0x3ffff000#32) ||| 0x80000000#32 }
      | 16, 0 => { s with cp0ConfigK0 := ccaWrite s.cp0ConfigK0 (v.setWidth 3),
                          cp0ConfigK23 := ccaWrite s.cp0ConfigK23 ((v >>> 28).setWidth 3),
                          cp0ConfigKU := ccaWrite s.cp0ConfigKU ((v >>> 25).setWidth 3) }
      | 16, 5 => { s with cp0Config5SBRI := v &&& 0x40#32 != 0#32 }
      | 17, 0 => { s with llBit := s.llBit && v &&& 1#32 != 0#32 }
      | 30, 0 => { s with cp0ErrorEpc := v }
      | 31, 2 => { s with cp0KScratch := fun j => if j = 0 then v else s.cp0KScratch j }
      | 31, 3 => { s with cp0KScratch := fun j => if j = 1 then v else s.cp0KScratch j }
      | 31, 4 => { s with cp0KScratch := fun j => if j = 2 then v else s.cp0KScratch j }
      | 31, 5 => { s with cp0KScratch := fun j => if j = 3 then v else s.cp0KScratch j }
      | 31, 6 => { s with cp0KScratch := fun j => if j = 4 then v else s.cp0KScratch j }
      | 31, 7 => { s with cp0KScratch := fun j => if j = 5 then v else s.cp0KScratch j }
      | _, _ => s := by
  unfold cp0WriteAt
  generalize rd.toNat = n
  generalize sel.toNat = m
  symm
  split <;> (try subst_vars) <;> try rfl
  · show s = (match cp0Layout .r6 n m with | some r => cp0Write s v r | none => s)
    cases h : cp0Layout .r6 n m with
    | none => rfl
    | some r =>
      unfold cp0Layout at h
      split at h <;> first | (simp_all; done) | (injection h with h; subst h; rfl)

/-- **`mfc0` through the layout table**: `$rt ← cp0ReadAt s rd sel` (the register `cp0Layout`
names for `(rd, sel)`, or 0), and `pc` advances (MD00086 Vol II-A Rev 6.06, MFC0, p.266). The
register-by-register form is `mfc0_spec_raw`. -/
theorem mfc0_spec_layout (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) (cp0ReadAt s rd sel)) with
          pc := (writeReg s (regIdxSpec rt) (cp0ReadAt s rd sel)).pc + 4#32 } := by
  cp0_step_spec

/-- **`mfc0` reads CP0 register `(rd, sel)` into GPR `$rt`**, for every `(rd, sel)` (`decode`
accepts them all), register by register (MD00090 Vol III Rev 6.02 Table 9.1 and the register
sections): `(4,2)` UserLocal (§9.11, p.143), `(7,0)` HWREna, `(8,0)` BadVAddr, `(8,1)` BadInstr
(§9.25, p.179), `(8,2)` BadInstrP (§9.26, p.181), `(9,0)` Count, `(11,0)` Compare, `(12,0)` Status,
`(12,1)` IntCtl (reads `0xE000_0000`: `IPTI = 7`, every other field 0, Table 9.48, p.199-201),
`(12,2)` SRSCtl (reads 0: `HSS = 0`, Table 9.49, p.203-204), `(13,0)` Cause, `(14,0)` EPC, `(15,0)`
PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1 (reads `0x8000_0001`: `M = 1`, `FP = 1`, Table
9.65, p.237-240), `(16,2)` Config2 (reads `0x8000_0000`: `M = 1`, no level 2/3 cache, Table 9.66,
p.241-243), `(16,3)` Config3 (reads `0x8C00_3000`: `M`, `BP`, `BI`, `ULRI`, `RXI`, §9.48, p.245-248),
`(16,4)` Config4 (reads `0x80FC_0000`: `M`, `KScrExist` = KScratch1..6, §9.49, p.253-255), `(16,5)`
Config5 (`XNP`, `LLB`, and the R/W `SBRI`, §9.50, p.259-264), `(17,0)` LLAddr (`LLB` = `LLbit` in bit
0, the address field not implemented, §9.52, Table 9.72, p.269-270), `(30,0)` ErrorEPC, `(31,2..7)`
KScratch1..6 (§9.70, p.311). `Cause` reads the stored bits plus the hardware interrupt lines in
`IP7..IP2` (`State.hwInt`) and the timer request: `TI` (bit 30) and, merged into it (`IntCtl.IPTI =
7` pin), `IP7` (bit 15) while a timer interrupt is pending (Table 9.52, p.209, 211; Table 6.2, p.73).
The read happens before the step's timer tick, so `Count` reads the value the step started with.
**Every other pair reads 0**: "Release 6: Reading a reserved register or a register that is not
implemented for the current core configuration returns 0" (MD00086 Vol II-A Rev 6.06, MFC0, p.266).
Coprocessor 0 must be usable (`hcp0`: Kernel Mode); otherwise see
`cp0_instruction_user_mode_unusable`. -/
theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 4, 2 => read s.cp0UserLocal
      | 7, 0 => read s.cp0HWREna
      | 8, 0 => read s.cp0BadVAddr
      | 8, 1 => read s.cp0BadInstr
      | 8, 2 => read s.cp0BadInstrP
      | 9, 0 => read s.cp0Count
      | 11, 0 => read s.cp0Compare
      | 12, 0 => read s.cp0Status
      | 12, 1 => read 0xE0000000#32
      | 12, 2 => read 0#32
      | 13, 0 => read (s.cp0Cause ||| (s.hwInt.setWidth 32 <<< 10) |||
          (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32))
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read (0x80000980#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) |||
          (s.cp0ConfigKU.setWidth 32 <<< 25) ||| s.cp0ConfigK0.setWidth 32)
      | 16, 1 => read 0x80000001#32
      | 16, 2 => read 0x80000000#32
      | 16, 3 => read 0x8C003000#32
      | 16, 4 => read 0x80FC0000#32
      | 16, 5 => read (0x00002010#32 ||| (if s.cp0Config5SBRI then 0x40#32 else 0#32))
      | 17, 0 => read (if s.llBit then 1#32 else 0#32)
      | 30, 0 => read s.cp0ErrorEpc
      | 31, 2 => read (s.cp0KScratch 0)
      | 31, 3 => read (s.cp0KScratch 1)
      | 31, 4 => read (s.cp0KScratch 2)
      | 31, 5 => read (s.cp0KScratch 3)
      | 31, 6 => read (s.cp0KScratch 4)
      | 31, 7 => read (s.cp0KScratch 5)
      | _, _ => read 0#32) := by
  rw [mfc0_spec_layout s w rt rd sel hfetch hdecode hpb hcp0 hexec, cp0ReadAt_eq]
  generalize rd.toNat = n
  generalize sel.toNat = m
  congr 1
  symm
  split <;> (try subst_vars) <;> try rfl

/-- **`mtc0` through the layout table**: `cp0WriteAt s rd sel $rt` (the write rule of the register
`cp0Layout` names for `(rd, sel)`, or nothing), and `pc` advances (MD00086 Vol II-A Rev 6.06, MTC0,
p.290). The register-by-register form is `mtc0_spec_raw`. -/
theorem mtc0_spec_layout (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (cp0WriteAt s rd sel (readReg s (regIdxSpec rt))) with pc := s.pc + 4#32 } := by
  have h : step s = timerTick (mkNext s (cp0WriteAt s rd sel (readReg s (regIdxSpec rt)))) := by
    cp0_step_spec
  rw [h]
  unfold mkNext advance
  rw [hpb]
  simp only [cp0WriteAt_pc]

/-- **`mtc0` writes GPR `$rt` into CP0 register `(rd, sel)`, through that register's field table**,
for every `(rd, sel)` (`decode` accepts them all). R/W in full: `UserLocal` (4,2; MD00090 Vol III
Rev 6.02 Table 9.19, p.143), `Count` (9,0: "can be written for functional or diagnostic purposes",
§9.27, p.183), `EPC` (14,0), `ErrorEPC` (30,0) and `KScratch1..6` (31,2..7; Table 9.84, p.311). A write
to `Compare` (11,0) stores the value and clears the timer interrupt (`Cause.TI`; §9.30, p.187).
`Status` (12,0) keeps only `statusWriteMask` (IE, EXL, ERL, UM, IM7..0, BEV, the Release 6 software
bit `RW` (28), CU1; every other bit reads as zero). `Cause` (13,0) changes only `causeWriteMask` (DC,
IV, IP1..0) and keeps `BD`, `CE`, `ExcCode` and everything else. `HWREna` (7,0) keeps bits 0..3, 5 and
29 (`hwrenaWriteMask`; Tables 9.39-9.40, p.175-176). `EBase` (15,1) takes bits 29..12 of the written
value under the fixed bits 31..30 = `10`. `Config` (16,0) takes `K23` (30..28), `KU` (27..25) and
`K0` (2..0), each only if the value is a supported cacheability attribute (`ccaWrite`: "For Release 6,
writes of unsupported values are ignored", Table 9.64, p.233, 235). `Config5` (16,5) takes only
`SBRI` (bit 6, R/W, Table 9.69, p.263). `LLAddr` (17,0) clears `LLbit` when bit 0 of the value is 0
and never sets it ("LLB can be cleared by software but cannot be set", Table 9.72, p.270). **Every
other pair is unchanged**: the read-only registers `BadVAddr`, `BadInstr`, `BadInstrP`, `IntCtl`,
`SRSCtl`, `PRId`, `Config1..4`, and every register the layout does not name ("Release 6: Writes to a
register that is reserved or not defined for the current core configuration are ignored", MD00086
Vol II-A Rev 6.06, MTC0, p.290). Coprocessor 0 must be usable (`hcp0`). -/
theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match rd.toNat, sel.toNat with
      | 4, 2 => { s with cp0UserLocal := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 7, 0 =>
        { s with cp0HWREna := readReg s (regIdxSpec rt) &&& hwrenaWriteMask, pc := s.pc + 4#32 }
      | 9, 0 => { s with cp0Count := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 11, 0 =>
        { s with cp0Compare := readReg s (regIdxSpec rt), cp0TimerInt := false, pc := s.pc + 4#32 }
      | 12, 0 =>
        { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 1 =>
        { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 =>
        { s with
              cp0ConfigK0 := ccaWrite s.cp0ConfigK0 ((readReg s (regIdxSpec rt)).setWidth 3)
              cp0ConfigK23 := ccaWrite s.cp0ConfigK23 ((readReg s (regIdxSpec rt) >>> 28).setWidth 3)
              cp0ConfigKU := ccaWrite s.cp0ConfigKU ((readReg s (regIdxSpec rt) >>> 25).setWidth 3)
              pc := s.pc + 4#32 }
      | 16, 5 =>
        { s with cp0Config5SBRI := readReg s (regIdxSpec rt) &&& 0x40#32 != 0#32, pc := s.pc + 4#32 }
      | 17, 0 =>
        { s with llBit := s.llBit && readReg s (regIdxSpec rt) &&& 1#32 != 0#32, pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 31, 2 => { s with cp0KScratch := fun j => if j = 0 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 3 => { s with cp0KScratch := fun j => if j = 1 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 4 => { s with cp0KScratch := fun j => if j = 2 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 5 => { s with cp0KScratch := fun j => if j = 3 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 6 => { s with cp0KScratch := fun j => if j = 4 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 7 => { s with cp0KScratch := fun j => if j = 5 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | _, _ => { s with pc := s.pc + 4#32 }) := by
  rw [mtc0_spec_layout s w rt rd sel hfetch hdecode hpb hcp0 hexec, cp0WriteAt_eq]
  generalize readReg s (regIdxSpec rt) = v
  generalize rd.toNat = n
  generalize sel.toNat = m
  congr 1
  symm
  split <;> (try subst_vars) <;> try rfl

/-- **`mfc0` of a register the layout does not name reads 0** (MD00086 Vol II-A Rev 6.06, MFC0,
p.266: "Release 6: Reading a reserved register or a register that is not implemented for the
current core configuration returns 0"). -/
theorem mfc0_unimplemented_reads_zero (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hnone : cp0Layout .r6 rd.toNat sel.toNat = none) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0#32) with pc := (writeReg s (regIdxSpec rt) 0#32).pc + 4#32 } := by
  rw [mfc0_spec_layout s w rt rd sel hfetch hdecode hpb hcp0 hexec]
  have h : cp0ReadAt s rd sel = 0#32 := by
    unfold cp0ReadAt; rw [show profile.release = .r6 from rfl, hnone]
  rw [h]

/-- **`mtc0` to a register the layout does not name changes nothing but `pc`** (MD00086 Vol II-A
Rev 6.06, MTC0, p.290: "Release 6: Writes to a register that is reserved or not defined for the
current core configuration are ignored"). -/
theorem mtc0_unimplemented_ignored (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hnone : cp0Layout .r6 rd.toNat sel.toNat = none) :
    step s = timerTick { s with pc := s.pc + 4#32 } := by
  rw [mtc0_spec_layout s w rt rd sel hfetch hdecode hpb hcp0 hexec]
  have h : cp0WriteAt s rd sel (readReg s (regIdxSpec rt)) = s := by
    unfold cp0WriteAt; rw [show profile.release = .r6 from rfl, hnone]
  rw [h]

/-- **`Config3` reads `0x8C00_3000`** (MD00090 Vol III Rev 6.02 §9.48, Table 9.67, p.245-248): `M`
(bit 31, Config4 present), `BP` (27: "Release 6: BadInstrP is always implemented"), `BI` (26:
"Release 6: BadInstr is always implemented"), `ULRI` (13: UserLocal), `RXI` (12); every other field
0; "All fields in the Config3 register are read-only" (p.245). -/
theorem mfc0_config3 (s : State) : cp0ReadAt s 16#32 3#32 = 0x8C003000#32 := rfl

/-- **`Config4` reads `0x80FC_0000`** (MD00090 Vol III Rev 6.02 §9.49, Table 9.68, p.253-255): `M`
(bit 31, Config5 present) and `KScrExist` = `0xFC` ("For Release 6, bits 2-7 are always 1 because
KScratch1-6 must be implemented", p.255); every other field 0. -/
theorem mfc0_config4 (s : State) : cp0ReadAt s 16#32 4#32 = 0x80FC0000#32 := rfl

/-- **`Config5` reads `0x2010` plus `SBRI`** (MD00090 Vol III Rev 6.02 §9.50, Table 9.69,
p.259-264): `XNP` (bit 13, no LLX/SCX), `LLB` (bit 4, "In Release 6, Config5LLB is read-only 1",
p.264), and `SBRI` (bit 6, R/W, reset 0, p.263). -/
theorem mfc0_config5 (s : State) :
    cp0ReadAt s 16#32 5#32 = 0x00002010#32 ||| (if s.cp0Config5SBRI then 0x40#32 else 0#32) := rfl

/-- **`Config5.SBRI` is the one writable bit of `Config5`**: `mtc0` stores bit 6 of the value into it
(MD00090 Vol III Rev 6.02 Table 9.69, p.263: SBRI "R/W"). -/
theorem mtc0_config5 (s : State) (v : W32) :
    cp0WriteAt s 16#32 5#32 v = { s with cp0Config5SBRI := v &&& 0x40#32 != 0#32 } := rfl

/-- **`LLAddr` reads `LLbit` in bit 0** (`LLB`) and 0 elsewhere (MD00090 Vol III Rev 6.02 §9.52,
Table 9.72, p.270: `LLB` is `LLbit`; the `PAddr` field's format "is implementation-dependent", and
"For the unimplemented address bits, writes are ignored and reads return zero": none implemented). -/
theorem mfc0_llAddr (s : State) : cp0ReadAt s 17#32 0#32 = if s.llBit then 1#32 else 0#32 := rfl

/-- **`mtc0` to `LLAddr` can clear `LLbit` but never set it** ("LLB can be cleared by software but
cannot be set", MD00090 Vol III Rev 6.02 Table 9.72, p.270): a value with bit 0 = 0 clears it; a
value with bit 0 = 1 leaves it as it was; nothing else changes. -/
theorem mtc0_llAddr (s : State) (v : W32) :
    cp0WriteAt s 17#32 0#32 v = { s with llBit := s.llBit && v &&& 1#32 != 0#32 } := rfl

/-- Corollary of `mtc0_llAddr`: writing a value with bit 0 = 0 to `LLAddr` clears `LLbit`. -/
theorem mtc0_llAddr_clears (s : State) (v : W32) (h : v &&& 1#32 = 0#32) :
    (cp0WriteAt s 17#32 0#32 v).llBit = false := by
  rw [mtc0_llAddr]; simp [h]

/-- Corollary of `mtc0_llAddr`: a write to `LLAddr` never sets `LLbit`. -/
theorem mtc0_llAddr_never_sets (s : State) (v : W32) (h : s.llBit = false) :
    (cp0WriteAt s 17#32 0#32 v).llBit = false := by
  rw [mtc0_llAddr]; simp [h]

/-- **`UserLocal` and the `KScratch` registers are plain storage**: what `mtc0` writes, `mfc0` reads
back (MD00090 Vol III Rev 6.02 Table 9.19, p.143: UserLocal "R/W"; Table 9.84, p.311: KScratch "R/W").
`k` is `KScratch(k+1)` at select `k + 2`. -/
theorem cp0_scratch_round_trip (s : State) (v : W32) (k : Fin 6) :
    cp0ReadAt (cp0WriteAt s 4#32 2#32 v) 4#32 2#32 = v ∧
      cp0ReadAt (cp0WriteAt s 31#32 (BitVec.ofNat 32 (k.val + 2)) v) 31#32
        (BitVec.ofNat 32 (k.val + 2)) = v := by
  refine ⟨rfl, ?_⟩
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

/-- The write mask of `Cause` is `DC` (27), `IV` (23), `IP1..IP0` (9..8)
(MD00090 Vol III Rev 6.02 §9.36, p.209-210). -/
theorem causeWriteMask_eq : causeWriteMask = 0x08800300#32 := rfl

/-- The write mask of `Status` is `CU1` (29), `RW` (28; `CU0` before Release 6), `BEV` (22),
`IM7..IM0` (15..8), `UM` (4), `ERL` (2), `EXL` (1), `IE` (0) (MD00090 Vol III Rev 6.02
§9.32, Table 9.47, p.190-196: the R/W fields of an implementation without
Supervisor Mode, coprocessors 2/3, `RP`, `FR`, `RE`, `MX`, `TS`, `SR`, `NMI`). -/
theorem statusWriteMask_eq : statusWriteMask = 0x3040ff17#32 := rfl

-- BEGIN R6-2
/-- The write mask of `HWREna` is bits 0..3 (`CPUNum`, `SYNCI_Step`, `CC`, `CCRes`), 5 (`XNP`) and 29
(`ULR`): the `rdhwr` registers the model implements; "If RDHWR register ‘n’ is not implemented, bit
‘n’ of this field returns a zero and is ignored on a write" (MD00090 Vol III Rev 6.02 Table 9.39,
p.175; Table 9.40, p.176: XNP "Required (Release 6)", "In Release 6, the UserLocal register is
required"). -/
theorem hwrenaWriteMask_eq : hwrenaWriteMask = 0x2000002F#32 := rfl
-- END R6-2

/-- **`di`: `$rt ← Status`, then `Status.IE ← 0`** (MD00086 Vol II-A
Rev 6.06, DI, p.164). The value written to `$rt` is the `Status` before the
change; no other `Status` bit changes. -/
theorem di_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.di rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 }) := by
  cp0_step_spec

/-- **`ei`: `$rt ← Status`, then `Status.IE ← 1`** (MD00086 Vol II-A
Rev 6.06, EI, p.176). -/
theorem ei_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ei rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 }) := by
  cp0_step_spec

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }) := by
  cp0_step_spec

-- BEGIN R6-2
/-- **`eretnc`** (MD00086 Vol II-A Rev 6.06, ERETNC, p.179-180), executed outside a delay slot: the
Operation of `eret` without `LLbit ← 0`: "ERETNC is identical to ERET except that an ERETNC will not
clear the LLbit that is set by execution of an LL instruction" (p.179): `if Status.ERL = 1 then PC ←
ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`. "ERETNC does not execute the next instruction (i.e., it
has no delay slot)" (p.179): `pc` is set in this very step. -/
theorem eretnc_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eretnc)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask }) := by
  cp0_step_spec

/-- **`eretnc` keeps `LLbit`** (MD00086 Vol II-A Rev 6.06, ERETNC, p.179: "ERETNC is identical to
ERET except that an ERETNC will not clear the LLbit"), whichever return address it uses. -/
theorem eretnc_keeps_llBit (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eretnc)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).llBit = s.llBit := by
  rw [eretnc_spec_raw s w hfetch hdecode hpb hcp0 hexec, timerTick_llBit]
  split <;> rfl

/-- **`eretnc` in a branch delay slot raises Reserved Instruction** ("Release 6 implementations are
required to signal a Reserved Instruction exception if ERETNC is executed in the delay slot or
Release 6 forbidden slot of a branch or jump instruction", MD00086 Vol II-A Rev 6.06, ERETNC,
p.179). -/
theorem eretnc_in_delay_slot_reserved_instruction (s : State) (w t : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eretnc)
    (hpb : s.pendingBranch = some t) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  branch_in_delay_slot_reserved_instruction s w .eretnc hfetch hdecode (by rw [hpb]; rfl) rfl hexec

/-- **`cache op, offset(base)`** (MD00086 Vol II-A Rev 6.06, CACHE, p.114-119): "vAddr ← GPR[base] +
sign_extend(offset); (pAddr, uncached) ← AddressTranslation(vAddr, DataReadReference)": the address
is translated (an Address Error, AdEL with `BadVAddr` = `vAddr`, if it fails) and then nothing else
happens. The model has no cache, so every operation/cache combination is unimplemented: "The
operation of this instruction is UNDEFINED for any operation/cache combination that is not
implemented. In Release 6, the instruction in this case should perform no operation" (p.119).
Coprocessor 0 must be usable (`hcp0`: "A COP0 or Cache instruction", MD00090 Vol III Rev 6.02
§6.2.22, p.100); otherwise see `cp0_instruction_user_mode_unusable`. -/
theorem cache_spec_raw (s : State) (w base op off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cache base op off))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match translate s (readReg s (regIdxSpec base) + signExt9 off) with
      | none => takeAddressException s excCodeAdEL (readReg s (regIdxSpec base) + signExt9 off)
      | some _ => { s with pc := s.pc + 4#32 }) := by
  have h : step s = timerTick (
      match translate s (readReg s (regIdxSpec base) + signExt9 off) with
      | none => takeAddressException s excCodeAdEL (readReg s (regIdxSpec base) + signExt9 off)
      | some _ => mkNext s s) := by
    cp0_step_spec
  rw [h]
  unfold mkNext advance
  rw [hpb]

/-- **`cache` is a no-op wherever it can execute**: coprocessor 0 is usable only in Kernel Mode
(`cp0Usable`), where every address translates (MD00090 Vol III Rev 6.02 Table 4.2, p.30; Fixed
Mapping MMU, §A.1, p.313), so the address check of `cache_spec_raw` never fails and the instruction
only advances `pc` ("In Release 6, the instruction in this case should perform no operation",
MD00086 Vol II-A Rev 6.06, CACHE, p.119). -/
theorem cache_noop (s : State) (w base op off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cache base op off))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick { s with pc := s.pc + 4#32 } := by
  rw [cache_spec_raw s w base op off hfetch hdecode hpb hcp0 hexec]
  have hk : kernelMode s = true := hcp0
  have hacc : accessAllowed s (readReg s (regIdxSpec base) + signExt9 off) = true := by
    simp [accessAllowed, hk]
  rw [translate_of_allowed s _ hacc]
-- END R6-2

/-- **`eret` clears `LLbit`**, whichever return address it uses — so an
`sc` after an exception return fails (see `sc_spec_raw`). -/
theorem eret_clears_llBit (s s' : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hstep : step s = s') (hexec : executesInstr s = true) :
    s'.llBit = false := by
  rw [← hstep, eret_spec_raw s w hfetch hdecode hpb hcp0 hexec, timerTick_llBit]
  split <;> rfl

/-- **`eret` in a branch delay slot raises Reserved Instruction**, like a
branch or jump there (pin): "Pre-Release 6: The operation of the processor is
UNDEFINED if an ERET is executed in the delay slot of a branch or jump
instruction" (MD00086 Vol II-A Rev 6.06, ERET, p.177); Release 6 requires
Reserved Instruction (same page). See `branch_in_delay_slot_reserved_instruction`. -/
theorem eret_in_delay_slot_reserved_instruction (s : State) (w t : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  branch_in_delay_slot_reserved_instruction s w .eret hfetch hdecode (by rw [hpb]; rfl) rfl hexec

/-- **`wait` completes and enters standby unless a request is already pending** (MD00086 Vol II-A
Rev 6.06, WAIT, p.442-443: "The WAIT instruction is implemented by stalling the pipeline at the
completion of the instruction and entering a lower power mode"; the Release 6 Operation stays in the
lower power mode `while (!interrupt_pending_and_not_masked_out() && ...)`, so with a request pending
and not masked out, `Cause.IP & Status.IM ≠ 0` (`interruptRequests`), the processor does not stop):
`pc` moves to the next instruction, which "execution continues with" once the pipeline restarts, and
`State.standby` is set exactly when no request is pending and not masked out (`Step.lean`'s `wait`
arm). The standby steps themselves: `Specs/Interrupt.lean` (`step_standby_stays`,
`step_standby_restarts`, `step_standby_interrupt`). -/
theorem wait_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with standby := interruptRequests s == 0#32, pc := s.pc + 4#32 }) := by
  cp0_step_spec

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` and `standby` is left
untouched. -/
theorem wait_preserves_state (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.physMem = s.physMem ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 ∧ s'.standby = (interruptRequests s == 0#32) := by
  refine ⟨_, wait_spec_raw s w code hfetch hdecode hpb hcp0 hexec, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- **`pause` with `LLbit` set records `EPC` = the next instruction and enters standby; with
`LLbit` clear it is a no-op** (MD00086 Vol II-A Rev 6.06, PAUSE, p.317: `if LLBit ≠ 0 then EPC ←
PC + 4; DescheduleInstructionStream() endif`). Pin (`Semantics/Exec/System.lean`): the
descheduled stream is the standby state after `wait` (`State.standby`, `pc` = the next
instruction); on this single hart nothing else clears `LLbit`, so only an interrupt or a reset
restarts it (`Specs/Interrupt.lean`). PAUSE is not a coprocessor-0 instruction: no `hcp0`. In a
delay slot it raises Reserved Instruction (`branch_in_delay_slot_reserved_instruction`). -/
theorem pause_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .pause)
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.llBit then { s with cp0Epc := s.pc + 4#32, standby := true, pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- Corollary of `pause_spec_raw`: with `LLbit` clear, `pause` only advances `pc`. -/
theorem pause_llbit_clear (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .pause)
    (hpb : s.pendingBranch = none) (hll : s.llBit = false) (hexec : executesInstr s = true) :
    step s = timerTick { s with pc := s.pc + 4#32 } := by
  rw [pause_spec_raw s w hfetch hdecode hpb hexec, hll]; rfl

/-- **`rdpgpr $rd, $rt`** (MD00086 Vol II-A Rev 6.06, RDPGPR, p.335: "GPR[rd] ← SGPR[SRSCtlPSS,
rt]"): with only the normal GPRs (`SRSCtl.HSS = 0`, `PSS = 0`, MD00090 Vol III Rev 6.02 Table 9.49,
p.203-204; "The normal GPRs are logically considered shadow set zero", §7, p.103), `$rd ← $rt`. -/
theorem rdpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) := by
  cp0_step_spec

/-- **`wrpgpr $rd, $rt`** (MD00086 Vol II-A Rev 6.06, WRPGPR, p.444: "SGPR[SRSCtlPSS, rd] ←
GPR[rt]"): with only the normal GPRs (`PSS = 0`), `$rd ← $rt`. -/
theorem wrpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wrpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) := by
  cp0_step_spec

/-! ## Coprocessor Unusable outside Kernel Mode -/

/-- A coprocessor-0 instruction does not use coprocessor 1 (the two guards of `execInstr` are
about disjoint instruction sets). -/
theorem usesCop1_of_usesCop0 (instr : Instruction) (h : usesCop0 instr = true) :
    usesCop1 instr = false := by
  cases instr <;> first | rfl | exact absurd h Bool.false_ne_true

-- BEGIN R6-2
/-- **Coprocessor 0 is usable exactly in Kernel Mode** (MD00090 Vol III Rev 6.02 §3.5.3, p.23:
"Access to Coprocessor 0 registers are enabled under any of the following conditions: The processor
is running in Kernel Mode or Debug Mode, as defined above. The CU0 bit in the Status register is 1."
Release 6 has no `CU0`: bit 28 of `Status` is the software bit `RW`, Table 9.47, p.190; Debug Mode
is not implemented). -/
theorem cp0Usable_iff_kernelMode (s : State) : cp0Usable s = true ↔ kernelMode s = true := Iff.rfl
-- END R6-2

/-- **Every coprocessor-0 instruction executed outside Kernel Mode raises Coprocessor Unusable with
`Cause.CE = 0`, and does nothing else.** The instructions are `usesCop0`: `mfc0`, `mtc0`, `di`,
`ei`, `eret`, `eretnc`, `wait`, `rdpgpr`, `wrpgpr`, `cache` (each page lists "Coprocessor Unusable"
among its exceptions: MD00086 Vol II-A Rev 6.06, MFC0 p.266, MTC0 p.291, DI p.164, EI p.176, ERET
p.178, ERETNC p.180, WAIT p.443, RDPGPR p.335, WRPGPR p.444, CACHE p.119). The rule: "A COP0 or
Cache instruction was executed while the processor was running in a mode other than Debug Mode or
Kernel Mode, and the CU0 bit in the Status register was a zero"; `Cause.CE` = "unit number of the
coprocessor being referenced" (MD00090 Vol III Rev 6.02 §6.2.22, p.100). Release 6 has no `CU0`, so
`cp0Usable s = false` is exactly User Mode (`cp0Usable_iff_kernelMode`; §3.2, p.21; §3.5.3, p.23).
The hypothesis `hnb` excludes `eret`/`eretnc`/`wait` in a delay slot, which raises Reserved
Instruction in every mode (`branch_in_delay_slot_reserved_instruction`). Undecodable COP0 words:
`step_reserved_cop0_unusable`. -/
theorem cp0_instruction_user_mode_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop0 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cp0Usable s = false) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeCpU 0#32) := by
  have h1 : (isBranchLike instr && s.pendingBranch.isSome) = false := by
    rcases hnb with h | h <;> simp [h]
  have h2 : usesCop1 instr = false := usesCop1_of_usesCop0 instr huses
  rw [step_of_executesInstr s hexec]; unfold execute; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  unfold execInstr
  rw [h1, h2, huses, hcu]
  rfl

-- `mfc0` reads back Status/Cause/EPC, selected by `rd`;
-- a register the layout does not name (here `(0, 0)`, Index: no TLB) reads 0 (Release 6).
#guard (let s := stepIn (prog1Spec (.mfc0 8#32 12#32 0#32)) { (initialState textBase) with cp0Status := 0x2#32 }
        readReg s 8 == 0x2#32) = true

#guard (let s := stepIn (prog1Spec (.mfc0 8#32 13#32 0#32)) { (initialState textBase) with cp0Cause := 0x34#32 }
        readReg s 8 == 0x34#32) = true

#guard (let s := stepIn (prog1Spec (.mfc0 8#32 14#32 0#32)) { (initialState textBase) with cp0Epc := 0x3000#32 }
        readReg s 8 == 0x3000#32) = true

#guard (let s' := stepIn (prog1Spec (.mfc0 8#32 0#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234#32)])
        readReg s' 8 == 0#32 && s'.pc == textBase + 4#32) = true

-- `mtc0` writes Status/Cause (through its mask)/EPC from a GPR; a write to a
-- register the layout does not name is ignored (Release 6).
#guard (let s := stepIn (prog1Spec (.mtc0 8#32 12#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x2#32)])
        s.cp0Status == 0x2#32) = true

#guard (let s := stepIn (prog1Spec (.mtc0 8#32 13#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        s.cp0Cause == causeWriteMask) = true

#guard (let s := stepIn (prog1Spec (.mtc0 8#32 14#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x3000#32)])
        s.cp0Epc == 0x3000#32) = true

#guard (let s0 := setRegsSpec (initialState textBase) [(8, 1#32)]
        let s' := stepIn (prog1Spec (.mtc0 8#32 0#32 0#32)) s0
        s'.pc == textBase + 4#32 && s'.cp0Status == s0.cp0Status && s'.cp0Cause == s0.cp0Cause &&
          s'.regs == s0.regs) = true

-- `eret` restores `pc` from `cp0Epc` and clears `Status.EXL`.
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask }
        s.pc == 0x3000#32 && s.cp0Status == 0#32) = true

-- `eret_clears_llBit`; `Status.ERL = 1` returns to `ErrorEPC` and clears `ERL`.
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask, llBit := true }
        s.llBit == false) = true

-- (run from kseg0: with `ERL = 1` kuseg is the identity map and executing from it is UNDEFINED,
-- MD00090 Vol III Rev 6.02 §A.1.2, p.316)
#guard (let s := stepIn (buildProgSpec 0x80001000#32 [.eret])
          { (initialState 0x80001000#32) with
              cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32, cp0Status := statusErlMask ||| statusExlMask }
        s.pc == 0x4000#32 && s.cp0Status == statusExlMask) = true

-- `eret_in_delay_slot_reserved_instruction`: Reserved Instruction taken in the
-- delay slot (`EPC` = the branch at `pc - 4`, `Cause.BD = 1`).
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with
            cp0Epc := 0x3000#32, pendingBranch := some 0x99999999#32 }
        causeExcCode s == excCodeRI && s.cp0Epc == textBase - 4#32 &&
          s.cp0Cause &&& causeBdMask == causeBdMask && s.pc == exceptionVectorAddr) = true

-- `wait` falls through to `pc + 4`, touching no other state (no request pending: standby).
#guard (let s := stepIn (prog1Spec (.wait 0#32)) (initialState textBase)
        s.pc == textBase + 4#32 && s.cp0Status == (initialState textBase).cp0Status &&
            s.regs == (initialState textBase).regs) = true

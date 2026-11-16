import Semantics.Exec.Base

/-!
# Exec.Cp0 — the coprocessor 0 registers and moves (MFC0, MTC0, DI, EI, RDPGPR, WRPGPR)

The coprocessor 0 register file of each release is a **table**, `cp0Layout`: it maps a register
number and select `(rd, sel)` to the register it names (`Cp0Reg`), or to nothing. `MFC0` and `MTC0`
consult it; each register's read value and write rule (its field table: which bits are R/W, which are
read-only or reserved) is `cp0Read` / `cp0Write`. A pair the table does not name is a register "that
is not implemented for the current core configuration": "Release 6: Reading a reserved register or a
register that is not implemented for the current core configuration returns 0" (MD00086 Vol II-A
Rev 6.06, MFC0, p.266) and writes to it "are ignored" (MTC0, p.290). The reset values are the Reset
exception's (`resetException`, `Step.lean`) and the power-on pins (`powerOnState`, `State.lean`).

The execution of the coprocessor 0 moves (`execBody`, `Step.lean`, dispatches here through
`execTables`): each arm is the instruction's effect after `execInstr`'s guards (no control transfer
in a delay slot; coprocessor 0 usable, i.e. Kernel Mode); `none` for every instruction of another
family.
-/

/-- **The coprocessor 0 registers** a release can have. `kscratch k` is `KScratch(k+1)`. -/
inductive Cp0Reg where
  | userLocal | hwrena | badVAddr | badInstr | badInstrP | count | compare | status | intCtl
  | srsCtl | cause | epc | prid | ebase | config | config1 | config2 | config3 | config4 | config5
  | llAddr | kscratch (k : Fin 6) | errorEpc
  deriving DecidableEq, Repr

/-- **The coprocessor 0 register layout of each release**: `(rd, sel)` ↦ the register, `none` for a
reserved or unimplemented register (MD00090 Vol III Rev 6.02 Table 9.1, p.111ff, by register):

| `(rd, sel)` | register | page |
|---|---|---|
| (4, 2) | UserLocal ("Release 6: Required") | §9.11, p.143 |
| (7, 0) | HWREna | §9.23, p.175 |
| (8, 0), (8, 1), (8, 2) | BadVAddr, BadInstr, BadInstrP ("Release 6 - Required") | §9.24-9.26, p.177-181 |
| (9, 0), (11, 0) | Count, Compare | §9.27, p.183; §9.30, p.187 |
| (12, 0), (12, 1), (12, 2) | Status, IntCtl, SRSCtl | §9.32-9.34, p.189-204 |
| (13, 0), (14, 0) | Cause, EPC | §9.36, p.209; §9.38, p.217 |
| (15, 0), (15, 1) | PRId, EBase | §9.40, p.221; §9.41, p.223 |
| (16, 0..5) | Config, Config1..Config5 | §9.45-9.50, p.233-264 |
| (17, 0) | LLAddr ("Required in Release 6") | §9.52, p.269 |
| (30, 0) | ErrorEPC | §9.68, p.307 |
| (31, 2..7) | KScratch1..6 ("Release 6 - Required") | §9.70, p.311 |

Not in the table, so reading 0 and ignoring writes: the TLB registers of the Fixed Mapping MMU
(Index, Random, EntryLo0/1, Context, PageMask, Wired, EntryHi: "For Release 6, writes to these
registers are ignored, reads return 0", Appendix A.1.3, p.317; PageGrain), and every optional register
of a module or feature this profile does not have (DECISIONS D5: watch, performance counters, EJTAG,
caches' TagLo/DataLo, Segmentation Control, ...). -/
def cp0Layout : Release → Nat → Nat → Option Cp0Reg
  | .r6, 4, 2 => some .userLocal
  | .r6, 7, 0 => some .hwrena
  | .r6, 8, 0 => some .badVAddr
  | .r6, 8, 1 => some .badInstr
  | .r6, 8, 2 => some .badInstrP
  | .r6, 9, 0 => some .count
  | .r6, 11, 0 => some .compare
  | .r6, 12, 0 => some .status
  | .r6, 12, 1 => some .intCtl
  | .r6, 12, 2 => some .srsCtl
  | .r6, 13, 0 => some .cause
  | .r6, 14, 0 => some .epc
  | .r6, 15, 0 => some .prid
  | .r6, 15, 1 => some .ebase
  | .r6, 16, 0 => some .config
  | .r6, 16, 1 => some .config1
  | .r6, 16, 2 => some .config2
  | .r6, 16, 3 => some .config3
  | .r6, 16, 4 => some .config4
  | .r6, 16, 5 => some .config5
  | .r6, 17, 0 => some .llAddr
  | .r6, 30, 0 => some .errorEpc
  | .r6, 31, 2 => some (.kscratch 0)
  | .r6, 31, 3 => some (.kscratch 1)
  | .r6, 31, 4 => some (.kscratch 2)
  | .r6, 31, 5 => some (.kscratch 3)
  | .r6, 31, 6 => some (.kscratch 4)
  | .r6, 31, 7 => some (.kscratch 5)
  | .r6, _, _ => none

/-- `LLAddr` as software reads it (MD00090 Vol III Rev 6.02 §9.52, Table 9.72, p.270): `LLB` (bit 0)
is `LLbit` ("This field allows the LLbit to be software accessible"); the `PAddr` field (31..1)
"encodes the physical address read by the most recent Load Linked instruction. The format of this
register is implementation-dependent, and an implementation may implement as many of the bits or format
the address in any way that it finds convenient", and "For the unimplemented address bits, writes are
ignored and reads return zero": the model implements none of them (pin), so they read 0. -/
def llAddrValue (s : State) : W32 := if s.llBit then 1#32 else 0#32

/-- **The value of CP0 register `r`** as `mfc0` reads it. -/
def cp0Read (s : State) : Cp0Reg → W32
  | .userLocal => s.cp0UserLocal
  | .hwrena => s.cp0HWREna
  | .badVAddr => s.cp0BadVAddr
  | .badInstr => s.cp0BadInstr
  | .badInstrP => s.cp0BadInstrP
  | .count => s.cp0Count
  | .compare => s.cp0Compare
  | .status => statusValue s  -- R6-5: `FR` reads 1 (`statusFrMask`)
  | .intCtl => intCtlValue
  | .srsCtl => srsCtlValue
  | .cause => causeValue s
  | .epc => s.cp0Epc
  | .prid => prIdValue
  | .ebase => ebaseValue s
  | .config => configValue s
  | .config1 => config1Value
  | .config2 => config2Value
  | .config3 => config3Value
  | .config4 => config4Value
  | .config5 => config5Value s
  | .llAddr => llAddrValue s
  | .kscratch k => s.cp0KScratch k
  | .errorEpc => s.cp0ErrorEpc

/-- A cacheability field write: the written value if it is supported, else the field is unchanged
("For Release 6, writes of unsupported values are ignored", MD00090 Vol III Rev 6.02 Table 9.64,
p.233, 235; `ccaSupported`). -/
def ccaWrite (old new : BitVec 3) : BitVec 3 := if ccaSupported new then new else old

/-- **The state after `mtc0` writes `v` to CP0 register `r`**, through the register's field table:

* fully R/W: `UserLocal` (Table 9.19, p.143), `Count` ("can be written for functional or diagnostic
  purposes", §9.27, p.183), `EPC`, `ErrorEPC`, `KScratch1..6` (Table 9.84, p.311);
* `Compare`: the value, and "as a side effect, clears the timer interrupt" (§9.30, p.187);
* `Status`: the `statusWriteMask` bits (the others read 0); `Cause`: only `DC`, `IV`, `IP1..IP0`
  (`causeWriteMask`; `WP`: "For Release 6, hardware ignores a write of 1", p.211, and no watch
  registers); `HWREna`: `hwrenaWriteMask`; `EBase`: the Exception Base field (29..12);
* `Config`: `K23`, `KU`, `K0` through `ccaWrite`; `Config5`: `SBRI` (bit 6) only;
* `LLAddr`: "LLB can be cleared by software but cannot be set" (Table 9.72, p.270): `LLbit ← LLbit
  and bit 0`; the `PAddr` field is not implemented (`llAddrValue`);
* read-only, the write is ignored: `BadVAddr` (Table 9.41, p.177), `BadInstr`, `BadInstrP` (Tables
  9.42, 9.43: R), `IntCtl` (no writable field here: `VS` "is ignored on write and reads as zero"
  without VI/EIC, Table 9.48, p.201), `SRSCtl` (with `HSS = 0` its fields can only hold 0, Table
  9.49, p.203-204; pin), `PRId`, `Config1`, `Config2` (`TU`/`SU` not implemented), `Config3` ("All
  fields in the Config3 register are read-only", p.245), `Config4`. -/
def cp0Write (s : State) (v : W32) : Cp0Reg → State
  | .userLocal => { s with cp0UserLocal := v }
  | .hwrena => { s with cp0HWREna := v &&& hwrenaWriteMask }
  | .count => { s with cp0Count := v }
  | .compare => { s with cp0Compare := v, cp0TimerInt := false }
  | .status => { s with cp0Status := v &&& statusWriteMask }
  | .cause => { s with cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) ||| (v &&& causeWriteMask) }
  | .epc => { s with cp0Epc := v }
  | .ebase => { s with cp0EBase := (v &&& ebaseWriteMask) ||| ebaseFixedBits }
  | .config => { s with cp0ConfigK0 := ccaWrite s.cp0ConfigK0 (v.setWidth 3),
                        cp0ConfigK23 := ccaWrite s.cp0ConfigK23 ((v >>> 28).setWidth 3),
                        cp0ConfigKU := ccaWrite s.cp0ConfigKU ((v >>> 25).setWidth 3) }
  | .config5 => { s with cp0Config5SBRI := v &&& 0x40#32 != 0#32 }
  | .llAddr => { s with llBit := s.llBit && v &&& 1#32 != 0#32 }
  | .kscratch k => { s with cp0KScratch := fun j => if j = k then v else s.cp0KScratch j }
  | .errorEpc => { s with cp0ErrorEpc := v }
  | .badVAddr | .badInstr | .badInstrP | .intCtl | .srsCtl | .prid | .config1 | .config2
  | .config3 | .config4 => s

/-- `MFC0`'s value for `(rd, sel)`: the register the layout of `profile.release` names, else 0. -/
def cp0ReadAt (s : State) (rd sel : W32) : W32 :=
  match cp0Layout profile.release rd.toNat sel.toNat with
  | some r => cp0Read s r
  | none => 0#32

/-- `MTC0`'s effect for `(rd, sel)`: the write to the register the layout names, else nothing. -/
def cp0WriteAt (s : State) (rd sel v : W32) : State :=
  match cp0Layout profile.release rd.toNat sel.toNat with
  | some r => cp0Write s v r
  | none => s

/-- The effect of the coprocessor 0 moves (MFC0, MTC0, DI, EI, RDPGPR, WRPGPR) and of DVP/EVP; `none`
for every other instruction. Outside Kernel Mode they raise Coprocessor Unusable before reaching this arm
(`execInstr`, `usesCop0`). -/
def execCp0 (s : State) : Instruction → Option State
  -- `mfc0 rt, rd, sel` (MFC0 p.266): `GPR[rt] ← CPR[0, rd, sel]`, or 0 (Release 6) for a register
  -- the layout does not name.
  | .mfc0 rt rd sel => some <| mkNext s (writeReg s (regIdx rt) (cp0ReadAt s rd sel))
  -- `mtc0 rt, rd, sel` (MTC0 p.290): `CPR[0, rd, sel] ← GPR[rt]` through the register's field
  -- table, or nothing (Release 6) for a register the layout does not name.
  | .mtc0 rt rd sel => some <| mkNext s (cp0WriteAt s rd sel (readReg s (regIdx rt)))
  -- `di`/`ei` (MD00086 Vol II-A Rev 6.06, DI p.164, EI p.176):
  -- `GPR[rt] ← Status; Status.IE ← 0` / `1`. The value written to `$rt` is
  -- the Status value *before* the change.
  | .di rt => some <|
    mkNext s (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdx rt)
      (statusValue s))
  | .ei rt => some <|
    mkNext s (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdx rt)
      (statusValue s))
  -- `rdpgpr rd, rt` / `wrpgpr rd, rt` (MD00086 Vol II-A Rev 6.06, RDPGPR p.335:
  -- "GPR[rd] ← SGPR[SRSCtlPSS, rt]"; WRPGPR p.444: "SGPR[SRSCtlPSS, rd] ← GPR[rt]").
  -- Only the normal GPRs exist (`SRSCtl.HSS = 0`: "only the normal GPRs are
  -- implemented", MD00090 Vol III Rev 6.02 Table 9.49, p.203), and "The normal
  -- GPRs are logically considered shadow set zero" (§7, p.103); `PSS` = `CSS` = 0
  -- (`srsCtlValue`), so `SGPR[0, r]` is `GPR[r]` and both are a register move.
  | .rdpgpr rd rt => some <| mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))
  | .wrpgpr rd rt => some <| mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))
  -- `dvp rt` / `evp rt` (MD00086 Vol II-A Rev 6.06, DVP p.172, EVP p.181): "For implementations that
  -- do not support multi-threading (Config5VP=0), this instruction must be treated as a NOP
  -- instruction"; `Config5.VP = 0` here (`config5Value`), so neither writes `GPR[rt]`.
  | .dvp _ | .evp _ => some (mkNext s s)
  | _ => none

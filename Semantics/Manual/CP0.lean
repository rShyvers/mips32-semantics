import Semantics.Manual.Pseudocode

/-!
# Manual.CP0 — coprocessor 0 registers, field by field

Every field is named by its bit position in the register's field table (MD00090 Vol III Rev 6.02
chapter 9); every write mask is built from the fields the table marks R/W under this profile. The
operating modes are §3.2-§3.4 (p.21-22).
-/

namespace Manual

/-- The word with exactly the bits `ps` set. -/
def bitsSet (ps : List Nat) : W32 := ps.foldl (fun w p => w ||| (1#32 <<< p)) 0#32

/-- The word with bits `hi..lo` set. -/
def fieldOnes (hi lo : Nat) : W32 := bitsSet ((List.range (hi + 1 - lo)).map (· + lo))

/-! ## Status (12, 0; §9.32, Figure 9.31 / Table 9.47, p.189-196) -/

/-- `StatusIE` (bit 0). -/
def StatusIE (a : Arch) : Bool := bit a.Status 0
/-- `StatusEXL` (bit 1). -/
def StatusEXL (a : Arch) : Bool := bit a.Status 1
/-- `StatusERL` (bit 2). -/
def StatusERL (a : Arch) : Bool := bit a.Status 2
/-- `StatusUM` (bit 4; "If Supervisor Mode is not implemented, this bit denotes the base operating
mode", Table 9.47, p.195). -/
def StatusUM (a : Arch) : Bool := bit a.Status 4
/-- `StatusIM7..IM0` (bits 15..8). -/
def StatusIM (a : Arch) : BitVec 8 := a.Status.extractLsb' 8 8
/-- `StatusBEV` (bit 22). -/
def StatusBEV (a : Arch) : Bool := bit a.Status 22
/-- `StatusRE` (bit 25), "Used to enable reverse-endian memory references while the processor is
running in user mode" (Table 9.47, p.192, "Optional (Pre-Release 6)"). Not implemented on this
profile, so it reads 0 whatever the register holds ("If this bit is not implemented, it must be
ignored on write and read as zero", p.192). -/
def StatusRE (_a : Arch) : Bool := false
/-- `StatusCU0` (bit 28). -/
def StatusCU0 (a : Arch) : Bool := bit a.Status 28
/-- `StatusCU1` (bit 29). -/
def StatusCU1 (a : Arch) : Bool := bit a.Status 29

/-- **The R/W bits of Status** on this profile (Table 9.47, p.189-196): `CU1`, `CU0` (29, 28), `BEV`
(22), `IM7..IM0` (15..8), `UM` (4), `ERL` (2), `EXL` (1), `IE` (0). `CU3`/`CU2` (no coprocessors 2,
3), `RP`, `FR` (32-bit FPU, reads 0), `RE`, `MX`, `TS`, `SR`, `NMI`, `ASE`, `Impl` are not implemented:
"returns zero on read ... ignored on write"; `R0` (3) reads 0. -/
def StatusWritable : W32 := bitsSet [0, 1, 2, 4, 22, 28, 29] ||| fieldOnes 15 8

/-! ## Operating modes (§3.2-§3.4, p.21-22) -/

/-- **Kernel Mode** (§3.2, p.21): "The KSU field in the CP0 Status register contains 0b00. The EXL
bit in the Status register is 1. The ERL bit in the Status register is 1." Without Supervisor Mode
`KSU = UM || R0` and `R0` reads 0. -/
def KernelMode (a : Arch) : Bool := !StatusUM a || StatusEXL a || StatusERL a

/-- **User Mode** (§3.4, p.22): "The KSU field in the Status register contains 0b10. The EXL and ERL
bits in the Status register are both 0." -/
def UserMode (a : Arch) : Bool := StatusUM a && !StatusEXL a && !StatusERL a

/-- **Coprocessor 0 is usable** (§3.5.3, p.23): "The processor is running in Kernel Mode or Debug
Mode ... The CU0 bit in the Status register is 1." -/
def CP0Usable (a : Arch) : Bool := KernelMode a || StatusCU0 a

/-! ## Cause (13, 0; §9.36, Table 9.52, p.209-212) -/

/-- `CauseIV` (bit 23). -/
def CauseIV (a : Arch) : Bool := bit a.Cause 23
/-- `CauseDC` (bit 27): "Disable Count register" (p.210). -/
def CauseDC (a : Arch) : Bool := bit a.Cause 27

/-- **The R/W bits of Cause** (Table 9.52, p.209-212): `DC` (27), `IV` (23), `IP1..IP0` (9..8). `BD`,
`TI`, `CE`, `PCI`, `IP7..IP2`, `ExcCode` are read-only; `WP`, `FDCI`, `PCI` are not implemented. -/
def CauseWritable : W32 := bitsSet [8, 9, 23, 27]

/-- `IntCtlIPTI` (bits 31..29 of IntCtl, §9.33, Table 9.48, p.199): "For Interrupt Compatibility and
Vectored Interrupt modes, this field specifies the IP number to which the Timer Interrupt request is
merged". -/
def IntCtlIPTI (i : Impl) : Nat := (i.IntCtl.extractLsb' 29 3).toNat

/-- **Cause as software reads it**: the stored bits, `TI` (bit 30, "Timer Interrupt", p.209),
`IP7..IP2` = the hardware interrupt requests `HW5..HW0` ("IP7..IP2 ... Hardware interrupt 5 ...
Hardware interrupt 0", p.211), and the timer request merged into `IP[IntCtlIPTI]` (Table 9.48,
p.199; Table 6.2, p.73). -/
def CauseRead (i : Impl) (a : Arch) : W32 :=
  a.Cause ||| (a.HW.setWidth 32 <<< 10) |||
    (if a.CauseTI then (1#32 <<< 30) ||| (1#32 <<< (8 + IntCtlIPTI i)) else 0#32)

/-! ## EBase (15, 1; §9.41, Figure 9.42 / Table 9.58, p.223-224) -/

/-- **EBase as software reads it** (Table 9.58, p.224): bit 31 reads 1 and bit 30 reads 0 ("This
bit must be written as a one, and returns one on read"; "... zero ..."), the Exception Base (29..12)
as stored, bits 11..10 and CPUNum (9..0) zero (one processor). -/
def EBaseRead (a : Arch) : W32 := (1#32 <<< 31) ||| (a.EBase &&& fieldOnes 29 12)

/-! ## Config (16, 0; §9.45, Table 9.64, p.233-235) -/

/-- **Config as software reads it**: the implementation's read-only fields with the three R/W
cacheability fields `K23` (30..28), `KU` (27..25), `K0` (2..0). -/
def ConfigRead (i : Impl) (a : Arch) : W32 :=
  i.ConfigFixed ||| (a.ConfigK23.setWidth 32 <<< 28) ||| (a.ConfigKU.setWidth 32 <<< 25) |||
    a.ConfigK0.setWidth 32

/-! ## HWREna (7, 0; §9.23, Table 9.39, p.175) -/

/-- **The R/W bits of HWREna**: one per implemented `RDHWR` register, 0..3 (`CPUNum`, `SYNCI_Step`,
`CC`, `CCRes`); "Each bit in this field enables access by the RDHWR instruction to a particular
hardware register"; unimplemented bits read 0 and ignore writes (Table 9.39, p.175). -/
def HWREnaWritable : W32 := fieldOnes 3 0

/-! ## `CPR[0, reg, sel]` -/

/-- **`IsCoprocessorRegisterImplemented(0, reg, sel)`** (MD00086 Vol II-A Rev 6.06, MTC0, p.290) on
this profile: `HWREna` (7,0), `BadVAddr` (8,0), `Count` (9,0), `Compare` (11,0), `Status` (12,0),
`IntCtl` (12,1), `SRSCtl` (12,2), `Cause` (13,0), `EPC` (14,0), `PRId` (15,0), `EBase` (15,1),
`Config` (16,0), `Config1` (16,1), `Config2` (16,2), `Config3` (16,3), `ErrorEPC` (30,0). Config3
is "Required if any optional feature described by this register is implemented: Release 2 of the
Architecture, ..." (MD00090 Vol III Rev 6.02 §9.48, p.245) and Config2 is "Required if ... the
Config3 register is required" (§9.47, p.241). Every other register is optional and absent
(docs/spec/COMPLIANCE.md §A). -/
def IsCoprocessorRegisterImplemented (reg sel : Nat) : Bool :=
  match reg, sel with
  | 7, 0 | 8, 0 | 9, 0 | 11, 0 | 12, 0 | 12, 1 | 12, 2 | 13, 0 | 14, 0 | 15, 0 | 15, 1 | 16, 0
  | 16, 1 | 16, 2 | 16, 3 | 30, 0 => true
  | _, _ => false

/-- **`CPR[0, reg, sel] ← data`** for an implemented register, field by field: R/W fields take the
written bits, read-only fields ignore the write (each register's field table). A write to `Compare`
"as a side effect, clears the timer interrupt" (§9.30, p.187). -/
def CPRWrite (reg sel : Nat) (data : W32) (a : Arch) : Arch :=
  match reg, sel with
  | 7, 0 => { a with HWREna := data &&& HWREnaWritable }
  | 9, 0 => { a with Count := data }
  | 11, 0 => { a with Compare := data, CauseTI := false }
  | 12, 0 => { a with Status := data &&& StatusWritable }
  | 13, 0 => { a with Cause := (a.Cause &&& ~~~CauseWritable) ||| (data &&& CauseWritable) }
  | 14, 0 => { a with EPC := data }
  | 15, 1 => { a with EBase := (1#32 <<< 31) ||| (data &&& fieldOnes 29 12) }
  | 16, 0 => { a with ConfigK0 := data.extractLsb' 0 3, ConfigK23 := data.extractLsb' 28 3,
                      ConfigKU := data.extractLsb' 25 3 }
  | 30, 0 => { a with ErrorEPC := data }
  | _, _ => a   -- BadVAddr, IntCtl, SRSCtl, PRId, Config1, Config2, Config3: read-only on this profile

/-- **The value of `CPR[0, reg, sel]`** for an implemented register. -/
def CPRRead (i : Impl) (reg sel : Nat) (a : Arch) : W32 :=
  match reg, sel with
  | 7, 0 => a.HWREna
  | 8, 0 => a.BadVAddr
  | 9, 0 => a.Count
  | 11, 0 => a.Compare
  | 12, 0 => a.Status
  | 12, 1 => i.IntCtl
  | 12, 2 => i.SRSCtl
  | 13, 0 => CauseRead i a
  | 14, 0 => a.EPC
  | 15, 0 => i.PRId
  | 15, 1 => EBaseRead a
  | 16, 0 => ConfigRead i a
  | 16, 1 => i.Config1
  | 16, 2 => i.Config2
  | 16, 3 => i.Config3
  | 30, 0 => a.ErrorEPC
  | _, _ => 0#32

end Manual

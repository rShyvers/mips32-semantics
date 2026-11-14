import Semantics.Manual.CP0

/-!
# Manual.Memory — address translation and the memory functions

MD00086 Vol II-A Rev 6.06 §2.2.2.2 (p.18-21): `AddressTranslation`, `LoadMemory`, `StoreMemory`,
`AccessLength` (Table 2.1, p.20-21); Table 1.1 (p.5): `BigEndianMem`, `BigEndianCPU`,
`ReverseEndian`. The MMU is the Fixed Mapping MMU (`Config.MT = 3`; MD00090 Vol III Rev 6.02
Appendix A.1, p.313-317) with the address error check of Table 4.2 (p.30).
-/

namespace Manual

/-- `IorD`: "Indicates whether access is for INSTRUCTION or DATA" (Figure 2.17, p.19). -/
inductive IorD where | INSTRUCTION | DATA
  deriving DecidableEq

/-- `LorS`: "Indicates whether access is for LOAD or STORE" (Figure 2.17, p.19). -/
inductive LorS where | LOAD | STORE
  deriving DecidableEq

/-- `AccessLength` names (Table 2.1, p.20-21): the value is the number of bytes minus one. -/
def BYTE : Nat := 0
/-- `HALFWORD` = 1 (Table 2.1). -/
def HALFWORD : Nat := 1
/-- `TRIPLEBYTE` = 2 (Table 2.1). -/
def TRIPLEBYTE : Nat := 2
/-- `WORD` = 3 (Table 2.1). -/
def WORD : Nat := 3

/-- `BigEndianMem` (Table 1.1, p.5): "Endian mode as configured at chip reset (0 → Little-Endian,
1 → Big-Endian)". This profile is big-endian (`Config.BE = 1`). -/
def BigEndianMem : Bool := true

/-- `ReverseEndian` (Table 1.1, p.5): "(SRRE and User mode)". -/
def ReverseEndian (a : Arch) : Bool := StatusRE a && UserMode a

/-- `BigEndianCPU` (Table 1.1, p.5): "(BigEndianMem XOR ReverseEndian)". -/
def BigEndianCPU (a : Arch) : Bool := BigEndianMem ^^ ReverseEndian a

/-- **Fixed Mapping translation** (MD00090 Vol III Rev 6.02 §A.1.1, p.313; Table A.1, p.313-314):
"Kseg0 and Kseg1 addresses ... both map to the low 512MB of physical memory"; "Useg/Suseg/Kuseg
addresses are mapped by adding 1GB to the virtual address when the ERL bit is zero in the Status
register, and are mapped using an identity mapping when the ERL bit is one"; "Sseg/Ksseg/Kseg2/Kseg3
addresses are mapped using an identity mapping". -/
def FixedMapping (erl : Bool) (vAddr : W32) : PAddr :=
  match vAddr.extractLsb' 29 3 with
  | 0b000#3 | 0b001#3 | 0b010#3 | 0b011#3 => if erl then vAddr else vAddr + 0x40000000#32
  | 0b100#3 | 0b101#3 => 0#3 ++ vAddr.extractLsb' 0 29
  | _ => vAddr

/-- **The cacheability attribute** of a reference (§A.1.2, Table A.2, p.316-317): `Config.K0` for
kseg0, uncached (2) for kseg1, `Config.KU` for kuseg, `Config.K23` for kseg2/kseg3. No cache exists on
this profile, so it selects nothing; it is computed to keep the pseudocode's shape. -/
def CCAOf (a : Arch) (vAddr : W32) : BitVec 3 :=
  match vAddr.extractLsb' 29 3 with
  | 0b100#3 => a.ConfigK0
  | 0b101#3 => 2#3
  | 0b110#3 | 0b111#3 => a.ConfigK23
  | _ => a.ConfigKU

/-- **`(pAddr, CCA) ← AddressTranslation(vAddr, IorD, LorS)`** (MD00086 Vol II-A Rev 6.06
§2.2.2.2.2, Figure 2.17, p.19; Figure 2.30, p.25: `vAddr ← memory_address(vAddr)` first). "If the
desired access is not permitted, the function fails and an exception is taken": with the Fixed
Mapping MMU "address error checking is still done before the translation process. Therefore, an
attempt to reference kseg0 from User Mode still results in an address error exception" (Vol III
§A.1.1, p.313). User Mode may reference useg only (Vol III Table 4.2, p.30); the Address Error is
AdEL for a load or fetch and AdES for a store, with `BadVAddr` = the failing address (§6.2.9,
p.92-93). -/
def AddressTranslation (vAddr : W32) (_iord : IorD) (lors : LorS) : Pseudo (PAddr × BitVec 3) := do
  let vAddr := memory_address vAddr
  let a ← Pseudo.get
  if UserMode a && bit vAddr 31 then
    match lors with
    | .LOAD => SignalException (.AddressErrorLoad vAddr)
    | .STORE => SignalException (.AddressErrorStore vAddr)
  else
    pure (FixedMapping (StatusERL a) vAddr, CCAOf a vAddr)

/-- The aligned word (`MemElem`) of physical memory that contains `pAddr`, big-endian
(`BigEndianMem = 1`): the byte at the lowest address is the most significant ("For big-endian
ordering this is the most-significant byte", §2.2.2.2, p.18). -/
def MemElemAt (m : PAddr → UInt8) (pAddr : PAddr) : W32 :=
  let base := pAddr &&& ~~~3#32
  (m base).toBitVec ++ (m (base + 1#32)).toBitVec ++ (m (base + 2#32)).toBitVec ++
    (m (base + 3#32)).toBitVec

/-- **`MemElem ← LoadMemory(CCA, AccessLength, pAddr, vAddr, IorD)`** (§2.2.2.2.3, Figure 2.18,
p.19): "The data is returned in a fixed-width naturally aligned memory element (MemElem) ... The
low-order 2 (or 3) bits of the address and the AccessLength indicate which of the bytes within
MemElem need to be passed to the processor." The whole aligned word is returned and the caller
selects the bytes, as each Operation does. A data load may make a following `SC` fail
(`Oracle.loadClearsLL`; MD00086 Vol II-A Rev 6.06, SC, p.347-348); an instruction fetch is not a
load of the sequence. -/
def LoadMemory (_cca : BitVec 3) (_accessLength : Nat) (pAddr : PAddr) (_vAddr : W32)
    (iord : IorD) : Pseudo W32 := do
  let a ← Pseudo.get
  let o ← Pseudo.oracle
  if iord == .DATA && o.loadClearsLL a then Pseudo.modify fun x => { x with LLbit := false }
  pure (MemElemAt a.Mem pAddr)

/-- The byte of the memory element `w` in byte lane `k` (0 = lowest address) for big-endian memory:
bits `31-8k .. 24-8k`. -/
def laneByte (w : W32) (k : Nat) : UInt8 := ⟨w.extractLsb' (24 - 8 * k) 8⟩

/-- Physical memory after writing byte `b` at `p`. -/
def updMem (m : PAddr → UInt8) (p : PAddr) (b : UInt8) : PAddr → UInt8 :=
  fun q => if p == q then b else m q

/-- **The byte lanes `StoreMemory` changes** (7B S2). The manual says only that "The low-order two (or
three) bits of pAddr and the AccessLength field indicate which of the bytes within the MemElem data
should be stored" (MD00086 Vol II-A Rev 6.06 §2.2.2.2.4, p.20) and gives AccessLength as "Length, in
bytes, of access" (Table 2.1, p.20-21: value = bytes - 1). For `p = pAddr1..0` and `a = AccessLength`
the stores of the pages need these lanes (lane 0 = lowest address = most significant byte of the
big-endian word): `SB`/`SH`/`SW` `p..p+a` (aligned, p+a <= 3); `SWL` (SWL p.398, Figure 5.10) `p..p+a`
with `a = 3 - p`, i.e. `p..3`; `SWR` (SWR p.402, Figure 5.14) lanes `0..p` with `a = p` (`WORD - byte`).
`p = a` occurs for no other store (SB, `a = 0 = p` selects lane 0 either way; SH/SW are aligned), so
the manual's two readings are told apart by `a = p`. This reading is recorded in SPEC-NOTES §11. -/
def storedLanes (p a : Nat) : List Nat :=
  if a == p then List.range (p + 1) else (List.range (a + 1)).map (p + ·)

/-- **`StoreMemory(CCA, AccessLength, MemElem, pAddr, vAddr)`** (§2.2.2.2.4, Figure 2.19, p.20):
"The low-order two (or three) bits of pAddr and the AccessLength field indicate which of the bytes
within the MemElem data should be stored; only these bytes in memory will actually be changed." The
bytes stored are `storedLanes`, each at its own address, in increasing address order. A store may
make a following `SC` fail (`Oracle.storeClearsLL`; SC p.347). -/
def StoreMemory (_cca : BitVec 3) (accessLength : Nat) (memElem : W32) (pAddr : PAddr)
    (_vAddr : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  Pseudo.modify fun a =>
    let base := pAddr &&& ~~~3#32
    let first := (pAddr &&& 3#32).toNat
    let mem := (storedLanes first accessLength).foldl
      (fun m l => updMem m (base + BitVec.ofNat 32 l) (laneByte memElem l)) a.Mem
    { a with Mem := mem, LLbit := if o.storeClearsLL a then false else a.LLbit }

/-- **Instruction fetch** (§2.2.2.4.2, Figure 2.29, p.25: "PC ← memory_address(PC); (instruction_data,
length) ← instruction_fetch(PC)"): an Address Error if the PC is not word aligned ("An instruction is
fetched from an address that is not aligned on a word boundary", Vol III §6.2.9, p.92; "both EPC and
BadVAddr point at the unaligned instruction address", p.93), then `AddressTranslation(PC,
INSTRUCTION, LOAD)` and `LoadMemory(CCA, WORD, pAddr, PC, INSTRUCTION)`. -/
def InstructionFetch : Pseudo W32 := do
  let pc := memory_address (← PC)
  if bits pc 1 0 != 0#2 then SignalException (.AddressErrorLoad pc)
  else
    let (pAddr, cca) ← AddressTranslation pc .INSTRUCTION .LOAD
    LoadMemory cca WORD pAddr pc .INSTRUCTION

end Manual

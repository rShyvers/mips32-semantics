import Semantics.Manual.Memory

/-!
# Manual.Ops.Memory — aligned loads and stores (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilots `LW` and `SW`. The alignment rule is in each page's Restrictions
section (the Release 6 Operation leaves it out: "The pseudocode is not completely adapted for Release 6
misalignment support"); it is transcribed as the first statement: this profile takes an Address Error
for every misaligned access ("Release 6 allows hardware to provide address misalignment support in lieu
of requiring natural alignment", e.g. LDC1 p.215; the pin of DECISIONS D3). **The misaligned-access
pin**: "Release 6 requires misaligned memory accesses to be supported by all Release 6-compliant
implementations for all ordinary memory instructions"; "The Release 6 requirement to support misaligned
memory accesses using trap and emulate is system-level, not necessarily hardware-level" (MD00082 Vol I-A
Rev 6.01 §4.5, p.44, an image page read in the PDF); "it is permitted for a processor implementation to produce the
Address Error exception for all misaligned accesses, with the appropriate exception handler software"
(Appendix B.2, p.128; "Whether an Address Error is generated is implementation-dependent", MD00090 Vol
III Rev 6.02 §6.2.9, p.92). This profile takes that option for every load and store; the alternative
is hardware support (Full Misalignment Support, p.128). `LL`/`SC` take the Address Error in every
implementation: "misalignment support is NOT provided for the load-linked/store conditional
instructions ... All such instructions continue to produce the Address Error exception if misaligned"
(p.128).
The byte-lane selection (`byte ← vAddr1..0 xor BigEndianCPU^2`) follows `BigEndianMem`, little-endian
on this profile (`Manual.BigEndianMem`).
-/

namespace Manual.Ops

open Manual

/-- **LW rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LW, p.235.
Restrictions: "Pre-Release 6: The effective address must be naturally-aligned. If either of the 2
least-significant bits of the address is non-zero, an Address Error exception occurs."
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
GPR[rt] ← memword
```
-/
def LW (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (load)
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    -- memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- GPR[rt] ← memword
    setGPR (reg rt) memword

/-- **SW rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SW, p.392.
Restrictions: "Pre-Release 6: The effective address must be naturally-aligned. If either of the 2
least-significant bits of the address is non-zero, an Address Error exception occurs."
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
dataword ← GPR[rt]
StoreMemory (CCA, WORD, dataword, pAddr, vAddr, DATA)
```
-/
def SW (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (store)
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- dataword ← GPR[rt]
    let dataword ← GPR (reg rt)
    -- StoreMemory (CCA, WORD, dataword, pAddr, vAddr, DATA)
    StoreMemory CCA WORD dataword pAddr vAddr

/-! ## 7B S2: the remaining byte, halfword and cache-hint pages -/

/-- **LB rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LB, p.211.
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
memword ← LoadMemory (CCA, BYTE, pAddr, vAddr, DATA)
byte ← vAddr1..0 xor BigEndianCPU2
GPR[rt] ← sign_extend(memword7+8*byte..8*byte)
```
Restrictions: "None". -/
def LB (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- memword ← LoadMemory (CCA, BYTE, pAddr, vAddr, DATA)
  let memword ← LoadMemory CCA BYTE pAddr vAddr .DATA
  -- byte ← vAddr1..0 xor BigEndianCPU^2
  let byte := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- GPR[rt] ← sign_extend(memword7+8*byte..8*byte)
  setGPR (reg rt) (sign_extend (memword.extractLsb' (8 * byte) 8))

/-- **LBU rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LBU, p.213.
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
memword ← LoadMemory (CCA, BYTE, pAddr, vAddr, DATA)
byte ← vAddr1..0 xor BigEndianCPU2
GPR[rt] ← zero_extend(memword7+8*byte..8*byte)
```
Restrictions: "None". -/
def LBU (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- memword ← LoadMemory (CCA, BYTE, pAddr, vAddr, DATA)
  let memword ← LoadMemory CCA BYTE pAddr vAddr .DATA
  -- byte ← vAddr1..0 xor BigEndianCPU^2
  let byte := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- GPR[rt] ← zero_extend(memword7+8*byte..8*byte)
  setGPR (reg rt) (zero_extend (memword.extractLsb' (8 * byte) 8))

/-- **LH rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LH, p.219.
Restrictions: "Pre-Release 6: The effective address must be naturally-aligned. If the
least-significant bit of the address is non-zero, an Address Error exception occurs."
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
memword ← LoadMemory (CCA, HALFWORD, pAddr, vAddr, DATA)
byte ← vAddr1..0 xor (BigEndianCPU || 0)
GPR[rt] ← sign_extend(memword15+8*byte..8*byte)
```
-/
def LH (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (load)
  if bit vAddr 0 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    let a ← Pseudo.get
    -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
    let pAddr := (pAddr &&& ~~~3#32) |||
      ((pAddr &&& 3#32) ^^^ (BitVec.ofBool (ReverseEndian a) ++ 0#1).setWidth 32)
    -- memword ← LoadMemory (CCA, HALFWORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA HALFWORD pAddr vAddr .DATA
    -- byte ← vAddr1..0 xor (BigEndianCPU || 0)
    let byte := (bits vAddr 1 0 ^^^ (BitVec.ofBool (BigEndianCPU a) ++ 0#1)).toNat
    -- GPR[rt] ← sign_extend(memword15+8*byte..8*byte)
    setGPR (reg rt) (sign_extend (memword.extractLsb' (8 * byte) 16))

/-- **LHU rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LHU, p.221.
Restrictions: "Pre-Release 6: The effective address must be naturally-aligned. If the
least-significant bit of the address is non-zero, an Address Error exception occurs."
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
memword ← LoadMemory (CCA, HALFWORD, pAddr, vAddr, DATA)
byte ← vAddr1..0 xor (BigEndianCPU || 0)
GPR[rt] ← zero_extend(memword15+8*byte..8*byte)
```
-/
def LHU (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (load)
  if bit vAddr 0 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    let a ← Pseudo.get
    -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
    let pAddr := (pAddr &&& ~~~3#32) |||
      ((pAddr &&& 3#32) ^^^ (BitVec.ofBool (ReverseEndian a) ++ 0#1).setWidth 32)
    -- memword ← LoadMemory (CCA, HALFWORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA HALFWORD pAddr vAddr .DATA
    -- byte ← vAddr1..0 xor (BigEndianCPU || 0)
    let byte := (bits vAddr 1 0 ^^^ (BitVec.ofBool (BigEndianCPU a) ++ 0#1)).toNat
    -- GPR[rt] ← zero_extend(memword15+8*byte..8*byte)
    setGPR (reg rt) (zero_extend (memword.extractLsb' (8 * byte) 16))

/-- **SB rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SB, p.344.
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
bytesel ← vAddr1..0 xor BigEndianCPU2
dataword ← GPR[rt]31-8*bytesel..0 || 0^(8*bytesel)
StoreMemory (CCA, BYTE, dataword, pAddr, vAddr, DATA)
```
Restrictions: "None". -/
def SB (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- bytesel ← vAddr1..0 xor BigEndianCPU^2
  let bytesel := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- dataword ← GPR[rt]31-8*bytesel..0 || 0^(8*bytesel)
  let dataword : W32 :=
    (low (← GPR (reg rt)) (32 - 8 * bytesel) ++ BitVec.zero (8 * bytesel)).setWidth 32
  -- StoreMemory (CCA, BYTE, dataword, pAddr, vAddr, DATA)
  StoreMemory CCA BYTE dataword pAddr vAddr

/-- **SH rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SH, p.373.
Restrictions: "Pre-Release 6: The effective address must be naturally-aligned. If the
least-significant bit of the address is non-zero, an Address Error exception occurs."
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
bytesel ← vAddr1..0 xor (BigEndianCPU || 0)
dataword ← GPR[rt]31-8*bytesel..0 || 0^(8*bytesel)
StoreMemory (CCA, HALFWORD, dataword, pAddr, vAddr, DATA)
```
-/
def SH (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (store)
  if bit vAddr 0 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    let a ← Pseudo.get
    -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor (ReverseEndian || 0))
    let pAddr := (pAddr &&& ~~~3#32) |||
      ((pAddr &&& 3#32) ^^^ (BitVec.ofBool (ReverseEndian a) ++ 0#1).setWidth 32)
    -- bytesel ← vAddr1..0 xor (BigEndianCPU || 0)
    let bytesel := (bits vAddr 1 0 ^^^ (BitVec.ofBool (BigEndianCPU a) ++ 0#1)).toNat
    -- dataword ← GPR[rt]31-8*bytesel..0 || 0^(8*bytesel)
    let dataword : W32 :=
      (low (← GPR (reg rt)) (32 - 8 * bytesel) ++ BitVec.zero (8 * bytesel)).setWidth 32
    -- StoreMemory (CCA, HALFWORD, dataword, pAddr, vAddr, DATA)
    StoreMemory CCA HALFWORD dataword pAddr vAddr

/-- **PREF hint, offset(base)** — MD00086 Vol II-A Rev 6.06, PREF, p.321 (Release 6 diagram: SPECIAL3,
9-bit offset in bits 15..7, function `110101`; Description) and p.323 (Operation).
```
vAddr ← GPR[base] + sign_extend(offset)
(pAddr, CCA) ← AddressTranslation(vAddr, DATA, LOAD)
Prefetch(CCA, pAddr, vAddr, DATA, hint)
```
Description (p.321): "Any action, including doing nothing, is permitted as long as it does not change
architecturally visible state or alter the meaning of a program"; "PREF does not cause
addressing-related exceptions, including TLB exceptions. If the address specified would cause an
addressing exception, the exception condition is ignored and no data movement occurs"; p.323:
"Prefetch does not take any TLB-related or address-related exceptions under any circumstances".
The implementation does nothing (a permitted action). So the translation, whose failure is ignored, and
`Prefetch` leave the state unchanged, and only the effective address is computed. The hints 24..31
(Table 5.2, p.322-323) are "not implemented in the Release 6 architecture and generate a Reserved
Instruction exception (RI)" (24, 26-29, 31: Reserved for Architecture; 25 writeback_invalidate and 30
PrepareForStore: "Reserved for Architecture in Release 6"); `Prefetch` with such a hint signals it.
Hints 0..23 are prefetches (2, 3 and their L2/L3 forms "behave as a NOP if not implemented", p.323). -/
def PREF (base hint offset : W32) : Pseudo Unit := do
  -- vAddr ← GPR[base] + sign_extend(offset)
  let _vAddr := (← GPR (reg base)) + sign_extend (imm9 offset)
  -- (pAddr, CCA) ← AddressTranslation(vAddr, DATA, LOAD): a failure is ignored (p.321)
  -- Prefetch(CCA, pAddr, vAddr, DATA, hint): hints 24..31 signal Reserved Instruction (Table 5.2,
  -- p.322-323); every other hint: no architecturally visible action (p.321)
  if 24 ≤ (low hint 5).toNat then SignalException .ReservedInstruction
  else pure ()

/-- **SYNC stype** — MD00086 Vol II-A Rev 6.06, SYNC, p.407 (diagram) and p.410 (Operation).
```
SyncOperation(stype)
```
Exceptions: "None" (p.410). `SyncOperation` "Perform[s] implementation-dependent operation to
complete the required synchronization operation" (Figure 2.21, p.21); on a strongly ordered
single-processor system "SYNC has the same effect as a NOP" (Programming Notes, p.410), the
implementation here. -/
def SYNC (_stype : W32) : Pseudo Unit := do
  -- SyncOperation(stype)
  pure ()

/-- **SYNCI offset(base)** — MD00086 Vol II-A Rev 6.06, SYNCI, p.412 (diagram) and p.413 (Operation).
```
vaddr ← GPR[base] + sign_extend(offset)
SynchronizeCacheLines(vaddr)      /* Operate on all caches */
```
Description (p.412): an Address Error exception (AdEL) "may occur if the effective address references a
portion of the kernel address space which would normally result in such an exception. It is
implementation dependent whether such an exception does occur" (`Impl.SynciAddressError`; the
implementation here: no); TLB, Cache Error and Bus Error exceptions are by-products of the cache and
bus actions, of which this implementation has none. `SynchronizeCacheLines` changes nothing (no
caches). -/
def SYNCI (base offset : W32) : Pseudo Unit := do
  -- vaddr ← GPR[base] + sign_extend(offset)
  let vaddr := (← GPR (reg base)) + sign_extend (imm16 offset)
  let impl ← Pseudo.impl
  let a ← Pseudo.get
  -- (Description) an implementation-dependent Address Error (AdEL) for a kernel address from User Mode
  if impl.SynciAddressError && UserMode a && bit vaddr 31 then SignalException (.AddressErrorLoad vaddr)
  -- SynchronizeCacheLines(vaddr)
  else pure ()

end Manual.Ops

import Semantics.Manual.Memory

/-!
# Manual.Ops.Unaligned — the load/store left/right family (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `LWL`.
-/

namespace Manual.Ops

open Manual

/-- **LWL rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LWL, p.240-241 (p.240, with the format
diagram, is image-only in the text extraction and was read from the PDF; the Operation is on p.241).
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
if BigEndianMem = 0 then
   pAddr ← pAddrPSIZE-1..2 || 0^2
endif
byte ← vAddr1..0 xor BigEndianCPU^2
memword ← LoadMemory (CCA, byte, pAddr, vAddr, DATA)
temp ← memword7+8*byte..0 || GPR[rt]23-8*byte..0
GPR[rt] ← temp
```
`GPR[rt]_{23-8*byte..0}` is the empty string when `byte = 3`. `x^2` (replication of a bit) is
`BitVec.fill 2 x` (Table 1.1, p.5: "x^y: Replication of bit value x into a y-bit string"). -/
def LWL (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- if BigEndianMem = 0 then pAddr ← pAddrPSIZE-1..2 || 0^2 endif
  let pAddr := if !BigEndianMem then pAddr &&& ~~~3#32 else pAddr
  -- byte ← vAddr1..0 xor BigEndianCPU^2
  let byte := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- memword ← LoadMemory (CCA, byte, pAddr, vAddr, DATA)
  let memword ← LoadMemory CCA byte pAddr vAddr .DATA
  -- temp ← memword7+8*byte..0 || GPR[rt]23-8*byte..0
  let temp : W32 := (low memword (8 + 8 * byte) ++ low (← GPR (reg rt)) (24 - 8 * byte)).setWidth 32
  -- GPR[rt] ← temp
  setGPR (reg rt) temp

end Manual.Ops

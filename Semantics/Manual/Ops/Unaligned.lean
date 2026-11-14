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

/-! ## 7B S2: LWR, SWL, SWR -/

/-- **LWR rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LWR, p.247-248 (p.247, with the format
diagram, is image-only in the text extraction; the Operation is on p.248).
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
if BigEndianMem = 0 then
   pAddr ← pAddrPSIZE-1..2 || 02
endif
byte ← vAddr1..0 xor BigEndianCPU2
memword ← LoadMemory (CCA, byte, pAddr, vAddr, DATA)
temp ← memword31..32-8*byte || GPR[rt]31–8*byte..0
GPR[rt] ← temp
```
**The printed `temp` line is wrong and is not transcribed** (SPEC-NOTES §11, "LWR"): as printed, a
big-endian `vAddr1..0 = 0` (`byte = 3`) gives `memword31..8 || GPR[rt]7..0`, and `vAddr1..0 = 3`
(`byte = 0`) leaves `GPR[rt]` unchanged, whereas Figure 4.6 on the same page (p.248) shows `e f g I`
for `vAddr1..0 = 0` and `I J K L` for `vAddr1..0 = 3`. The line is the mirror image of the LWL line
(LWL p.241: `memword7+8*byte..0 || GPR[rt]23-8*byte..0`, the loaded bytes first). The rows of Figure 4.6
(big-endian) are reproduced by `temp ← GPR[rt]31..32-8*byte || memword31..8*byte`
(`byte = 3 - vAddr1..0`: `e f g I`, `e f I J`, `e I J K`, `I J K L`), which is what is written below. -/
def LWR (base rt offset : W32) : Pseudo Unit := do
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
  -- temp ← GPR[rt]31..32-8*byte || memword31..8*byte   (see the note above on the printed line)
  let rtv ← GPR (reg rt)
  let temp : W32 :=
    (rtv.extractLsb' (32 - 8 * byte) (8 * byte) ++ memword.extractLsb' (8 * byte) (32 - 8 * byte)).setWidth 32
  -- GPR[rt] ← temp
  setGPR (reg rt) temp

/-- **SWL rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SWL, p.397-398 (Operation on p.398).
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
If BigEndianMem = 0 then
   pAddr ← pAddrPSIZE-1..2 || 02
endif
byte ← vAddr1..0 xor BigEndianCPU2
dataword ← 0^(24-8*byte) || GPR[rt]31..24-8*byte
StoreMemory(CCA, byte, dataword, pAddr, vAddr, DATA)
```
`StoreMemory` stores the lanes `pAddr1..0 .. pAddr1..0 + byte` of the aligned word (Figure 5.10:
big-endian `vAddr1..0 = 1` stores `E F G` in bytes 1..3; see `Manual.storedLanes`). -/
def SWL (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- If BigEndianMem = 0 then pAddr ← pAddrPSIZE-1..2 || 0^2 endif
  let pAddr := if !BigEndianMem then pAddr &&& ~~~3#32 else pAddr
  -- byte ← vAddr1..0 xor BigEndianCPU^2
  let byte := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- dataword ← 0^(24-8*byte) || GPR[rt]31..24-8*byte
  let rtv ← GPR (reg rt)
  let dataword : W32 := (BitVec.zero (24 - 8 * byte) ++ rtv.extractLsb' (24 - 8 * byte) (8 + 8 * byte)).setWidth 32
  -- StoreMemory(CCA, byte, dataword, pAddr, vAddr, DATA)
  StoreMemory CCA byte dataword pAddr vAddr

/-- **SWR rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SWR, p.401-402 (Operation on p.402).
```
vAddr ← sign_extend(offset) + GPR[base]
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian2)
If BigEndianMem = 0 then
   pAddr ← pAddrPSIZE-1..2 || 02
endif
byte ← vAddr1..0 xor BigEndianCPU2
dataword ← GPR[rt]31–8*byte..0 || 0^(8*byte)
StoreMemory(CCA, WORD-byte, dataword, pAddr, vAddr, DATA)
```
`StoreMemory` stores the lanes `0 .. pAddr1..0` of the aligned word for a big-endian `WORD-byte`
(Figure 5.14: big-endian `vAddr1..0 = 1` stores `G H` in bytes 0..1; see `Manual.storedLanes`). -/
def SWR (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
  let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
  let a ← Pseudo.get
  -- pAddr ← pAddrPSIZE-1..2 || (pAddr1..0 xor ReverseEndian^2)
  let pAddr := (pAddr &&& ~~~3#32) ||| ((pAddr &&& 3#32) ^^^ (BitVec.fill 2 (ReverseEndian a)).setWidth 32)
  -- If BigEndianMem = 0 then pAddr ← pAddrPSIZE-1..2 || 0^2 endif
  let pAddr := if !BigEndianMem then pAddr &&& ~~~3#32 else pAddr
  -- byte ← vAddr1..0 xor BigEndianCPU^2
  let byte := (bits vAddr 1 0 ^^^ BitVec.fill 2 (BigEndianCPU a)).toNat
  -- dataword ← GPR[rt]31-8*byte..0 || 0^(8*byte)
  let dataword : W32 := (low (← GPR (reg rt)) (32 - 8 * byte) ++ BitVec.zero (8 * byte)).setWidth 32
  -- StoreMemory(CCA, WORD-byte, dataword, pAddr, vAddr, DATA)
  StoreMemory CCA (WORD - byte) dataword pAddr vAddr

end Manual.Ops

import Semantics.Manual.Memory
import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuMemory — FP loads and stores (MD00086 Vol II-A Rev 6.06), 7B S4

`LWC1`, `SWC1`, `LDC1`, `SDC1`, `LWXC1`, `SWXC1`, `LDXC1`, `SDXC1`, `PREFX`. The pre-Release 6
alignment rule is in each page's Restrictions ("An Address Error exception occurs if
EffectiveAddress1..0 != 0", or 2..0 for a doubleword); it is transcribed as the first statement, as
`LW` does. The doubleword accesses do two word accesses, the least-significant word at the
address `xor`ed with `(BigEndianCPU xor ReverseEndian) || 0^2` (the pages write `paddr` for `pAddr`).
-/

namespace Manual.Ops

open Manual

/-- **LWC1 ft, offset(base)** — MD00086 Vol II-A Rev 6.06, LWC1, p.236.
```
vAddr <- sign_extend(offset) + GPR[base]
(pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
memword <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
StoreFPR(ft, UNINTERPRETED_WORD, memword)
```
Restrictions: "Pre-Release 6: An Address Error exception occurs if EffectiveAddress1..0 != 0 (not
word-aligned)." -/
def LWC1 (base ft offset : W32) : Pseudo Unit := do
  -- vAddr <- sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (load)
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    -- memword <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- StoreFPR(ft, UNINTERPRETED_WORD, memword)
    StoreFPR32 (reg ft) memword

/-- **SWC1 ft, offset(base)** — MD00086 Vol II-A Rev 6.06, SWC1, p.393.
```
vAddr <- sign_extend(offset) + GPR[base]
(pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
dataword <- ValueFPR(ft, UNINTERPRETED_WORD)
StoreMemory(CCA, WORD, dataword, pAddr, vAddr, DATA)
```
Restrictions: "Pre-Release 6: An Address Error exception occurs if EffectiveAddress1..0 != 0". -/
def SWC1 (base ft offset : W32) : Pseudo Unit := do
  -- vAddr <- sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (store)
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- dataword <- ValueFPR(ft, UNINTERPRETED_WORD)
    let dataword ← ValueFPR32 (reg ft)
    -- StoreMemory(CCA, WORD, dataword, pAddr, vAddr, DATA)
    StoreMemory CCA WORD dataword pAddr vAddr

/-- **LDC1 ft, offset(base)** — MD00086 Vol II-A Rev 6.06, LDC1, p.215.
```
vAddr <- sign_extend(offset) + GPR[base]
(pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
memlsw <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
paddr <- paddr xor 0b100
memmsw <- LoadMemory(CCA, WORD, pAddr, vAddr+4, DATA)
memdoubleword <- memmsw || memlsw
StoreFPR(ft, UNINTERPRETED_DOUBLEWORD, memdoubleword)
```
Restrictions: "Pre-Release 6: An Address Error exception occurs if EffectiveAddress2..0 != 0 (not
doubleword-aligned)." -/
def LDC1 (base ft offset : W32) : Pseudo Unit := do
  -- vAddr <- sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (load)
  if bits vAddr 2 0 != 0#3 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    let a ← Pseudo.get
    -- paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
    let pAddr := pAddr ^^^ ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32)
    -- memlsw <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
    let memlsw ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- paddr <- paddr xor 0b100
    let pAddr := pAddr ^^^ 0b100#32
    -- memmsw <- LoadMemory(CCA, WORD, pAddr, vAddr+4, DATA)
    let memmsw ← LoadMemory CCA WORD pAddr (vAddr + 4#32) .DATA
    -- memdoubleword <- memmsw || memlsw
    let memdoubleword := memmsw ++ memlsw
    -- StoreFPR(ft, UNINTERPRETED_DOUBLEWORD, memdoubleword)
    StoreFPR64 (reg ft) memdoubleword

/-- **SDC1 ft, offset(base)** — MD00086 Vol II-A Rev 6.06, SDC1, p.362.
```
vAddr <- sign_extend(offset) + GPR[base]
(pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
datadoubleword <- ValueFPR(ft, UNINTERPRETED_DOUBLEWORD)
paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
StoreMemory(CCA, WORD, datadoubleword31..0, pAddr, vAddr, DATA)
paddr <- paddr xor 0b100
StoreMemory(CCA, WORD, datadoubleword63..32, pAddr, vAddr+4, DATA)
```
Restrictions: "Pre-Release 6: An Address Error exception occurs if EffectiveAddress2..0 != 0". -/
def SDC1 (base ft offset : W32) : Pseudo Unit := do
  -- vAddr <- sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm16 offset) + (← GPR (reg base))
  -- (Restrictions) misaligned: Address Error (store)
  if bits vAddr 2 0 != 0#3 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- datadoubleword <- ValueFPR(ft, UNINTERPRETED_DOUBLEWORD)
    let datadoubleword ← ValueFPR64 (reg ft)
    let a ← Pseudo.get
    -- paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
    let pAddr := pAddr ^^^ ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32)
    -- StoreMemory(CCA, WORD, datadoubleword31..0, pAddr, vAddr, DATA)
    StoreMemory CCA WORD (bits datadoubleword 31 0) pAddr vAddr
    -- paddr <- paddr xor 0b100
    let pAddr := pAddr ^^^ 0b100#32
    -- StoreMemory(CCA, WORD, datadoubleword63..32, pAddr, vAddr+4, DATA)
    StoreMemory CCA WORD (bits datadoubleword 63 32) pAddr (vAddr + 4#32)

/-- **LWXC1 fd, index(base)** — MD00086 Vol II-A Rev 6.06, LWXC1, p.254.
```
vAddr <- GPR[base] + GPR[index]
if vAddr1..0 != 0^2 then SignalException(AddressError) endif
(pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
memword <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
StoreFPR(fd, UNINTERPRETED_WORD, memword)
``` -/
def LWXC1 (fd index base : W32) : Pseudo Unit := do
  -- vAddr <- GPR[base] + GPR[index]
  let vAddr := (← GPR (reg base)) + (← GPR (reg index))
  -- if vAddr1..0 != 0^2 then SignalException(AddressError) endif
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    -- memword <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- StoreFPR(fd, UNINTERPRETED_WORD, memword)
    StoreFPR32 (reg fd) memword

/-- **SWXC1 fs, index(base)** — MD00086 Vol II-A Rev 6.06, SWXC1, p.406.
```
vAddr <- GPR[base] + GPR[index]
if vAddr1..0 != 0^3 then SignalException(AddressError) endif
(pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
dataword <- ValueFPR(fs, UNINTERPRETED_WORD)
StoreMemory(CCA, WORD, dataword, pAddr, vAddr, DATA)
```
(The page prints `0^3` for the 2-bit test; the Restrictions say "EffectiveAddress1..0 != 0".) -/
def SWXC1 (fs index base : W32) : Pseudo Unit := do
  -- vAddr <- GPR[base] + GPR[index]
  let vAddr := (← GPR (reg base)) + (← GPR (reg index))
  -- if vAddr1..0 != 0 then SignalException(AddressError) endif
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- dataword <- ValueFPR(fs, UNINTERPRETED_WORD)
    let dataword ← ValueFPR32 (reg fs)
    -- StoreMemory(CCA, WORD, dataword, pAddr, vAddr, DATA)
    StoreMemory CCA WORD dataword pAddr vAddr

/-- **LDXC1 fd, index(base)** — MD00086 Vol II-A Rev 6.06, LDXC1, p.218.
```
vAddr <- GPR[base] + GPR[index]
if vAddr2..0 != 0^3 then SignalException(AddressError) endif
(pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
memlsw <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
paddr <- paddr xor 0b100
memmsw <- LoadMemory(CCA, WORD, pAddr, vAddr+4, DATA)
memdoubleword <- memmsw || memlsw
StoreFPR(fd, UNINTERPRETED_DOUBLEWORD, memdoubleword)
``` -/
def LDXC1 (fd index base : W32) : Pseudo Unit := do
  -- vAddr <- GPR[base] + GPR[index]
  let vAddr := (← GPR (reg base)) + (← GPR (reg index))
  -- if vAddr2..0 != 0^3 then SignalException(AddressError) endif
  if bits vAddr 2 0 != 0#3 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    let a ← Pseudo.get
    -- paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
    let pAddr := pAddr ^^^ ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32)
    -- memlsw <- LoadMemory(CCA, WORD, pAddr, vAddr, DATA)
    let memlsw ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- paddr <- paddr xor 0b100
    let pAddr := pAddr ^^^ 0b100#32
    -- memmsw <- LoadMemory(CCA, WORD, pAddr, vAddr+4, DATA)
    let memmsw ← LoadMemory CCA WORD pAddr (vAddr + 4#32) .DATA
    -- memdoubleword <- memmsw || memlsw
    let memdoubleword := memmsw ++ memlsw
    -- StoreFPR(fd, UNINTERPRETED_DOUBLEWORD, memdoubleword)
    StoreFPR64 (reg fd) memdoubleword

/-- **SDXC1 fs, index(base)** — MD00086 Vol II-A Rev 6.06, SDXC1, p.364.
```
vAddr <- GPR[base] + GPR[index]
if vAddr2..0 != 0^3 then SignalException(AddressError) endif
(pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
datadoubleword <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)
paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
StoreMemory(CCA, WORD, datadoubleword31..0, pAddr, vAddr, DATA)
paddr <- paddr xor 0b100
StoreMemory(CCA, WORD, datadoubleword63..32, pAddr, vAddr+4, DATA)
``` -/
def SDXC1 (fs index base : W32) : Pseudo Unit := do
  -- vAddr <- GPR[base] + GPR[index]
  let vAddr := (← GPR (reg base)) + (← GPR (reg index))
  -- if vAddr2..0 != 0^3 then SignalException(AddressError) endif
  if bits vAddr 2 0 != 0#3 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) <- AddressTranslation(vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- datadoubleword <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)
    let datadoubleword ← ValueFPR64 (reg fs)
    let a ← Pseudo.get
    -- paddr <- paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)
    let pAddr := pAddr ^^^ ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32)
    -- StoreMemory(CCA, WORD, datadoubleword31..0, pAddr, vAddr, DATA)
    StoreMemory CCA WORD (bits datadoubleword 31 0) pAddr vAddr
    -- paddr <- paddr xor 0b100
    let pAddr := pAddr ^^^ 0b100#32
    -- StoreMemory(CCA, WORD, datadoubleword63..32, pAddr, vAddr+4, DATA)
    StoreMemory CCA WORD (bits datadoubleword 63 32) pAddr (vAddr + 4#32)

/-- **PREFX hint, index(base)** — MD00086 Vol II-A Rev 6.06, PREFX, p.329.
```
vAddr <- GPR[base] + GPR[index]
(pAddr, CCA) <- AddressTranslation(vAddr, DATA, LOAD)
Prefetch(CCA, pAddr, vAddr, DATA, hint)
```
"Refer to the PREF instruction for all other details": "PREF does not cause addressing-related
exceptions, including TLB exceptions. If the address specified would cause an addressing exception,
the exception condition is ignored and no data movement occurs" (PREF, p.321), and "Any action,
including doing nothing, is permitted as long as it does not change architecturally visible state"
(p.321). So the translation is not performed here (its only effect would be that ignored exception)
and `Prefetch` is no action; the Operation changes no architectural state. -/
def PREFX (_hint index base : W32) : Pseudo Unit := do
  -- vAddr <- GPR[base] + GPR[index]
  let _vAddr := (← GPR (reg base)) + (← GPR (reg index))
  -- (pAddr, CCA) <- AddressTranslation(vAddr, DATA, LOAD); Prefetch(CCA, pAddr, vAddr, DATA, hint)
  pure ()

end Manual.Ops

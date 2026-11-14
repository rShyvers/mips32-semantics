import Semantics.Manual.Memory

/-!
# Manual.Ops.Memory — aligned loads and stores (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilots `LW` and `SW`. The pre-Release-6 alignment rule is in each page's
Restrictions section (the Release 6 Operation leaves it out: "The pseudocode is not completely adapted
for Release 6 misalignment support"); it is transcribed as the first statement.
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

end Manual.Ops

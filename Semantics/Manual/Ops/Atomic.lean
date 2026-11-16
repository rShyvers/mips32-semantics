import Semantics.Manual.Memory

/-!
# Manual.Ops.Atomic — LL and SC (MD00086 Vol II-A Rev 6.06)

Release 6 diagrams: SPECIAL3 with a 9-bit offset in bits 15..7 (`LL`
function `110110`, p.223; `SC` function `100110`, p.347). "Release 6 implements a 9-bit offset" (LL,
Programming Notes, p.224): `sign_extend(offset)` extends the 9-bit field (`imm9`).
-/

namespace Manual.Ops

open Manual

/-- **LL rt, offset(base)** — MD00086 Vol II-A Rev 6.06, LL, p.223-224 (Release 6 diagram and the first lines
of the Operation on p.223, the rest on p.224).
```
vAddr ← sign_extend(offset) + GPR[base]
if vAddr1..0 ≠ 02 then
   SignalException(AddressError)
endif
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
GPR[rt] ← memword
LLbit ← 1
```
Description (p.223): "This begins a RMW sequence on the current processor. There can be only one
active RMW sequence per processor. When an LL is executed it starts an active RMW sequence replacing
any other sequence that was active." `SC` compares its own address with "that of the preceding LL"
(SC, p.347), so the `LL` also records its aligned address, `LLAddr` (`Manual.Arch.LLAddr`); the manual's
Operation does not name that state. -/
def LL (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm9 offset) + (← GPR (reg base))
  -- if vAddr1..0 ≠ 0^2 then SignalException(AddressError) endif
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    -- memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- GPR[rt] ← memword
    setGPR (reg rt) memword
    -- LLbit ← 1   (and the address of the sequence, for the SC comparison, SC p.347)
    Pseudo.modify fun a => { a with LLbit := true, LLAddr := vAddr }

/-- **SC rt, offset(base)** — MD00086 Vol II-A Rev 6.06, SC, p.347-349 (Release 6 diagram p.347, Operation on p.349).
```
vAddr ← sign_extend(offset) + GPR[base]
if vAddr1..0 ≠ 02 then
   SignalException(AddressError)
endif
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
dataword ← GPR[rt]
if LLbit then
   StoreMemory (CCA, WORD, dataword, pAddr, vAddr, DATA)
endif
GPR[rt] ← 031 || LLbit
LLbit ← 0 // if Config5LLB=1, SC always clears LLbit regardless of address match.
```
The Description (p.347) is `if atomic_update then memory[GPR[base] + offset] ← GPR[rt], GPR[rt] ← 1
else GPR[rt] ← 0`, and "an SC must always compare its address against that of the LL. An SC will
fail if the aligned address of the SC does not match that of the preceding LL"; the Operation tests
`LLbit` only. `atomic_update` is therefore `LLbit` with the address comparison (`vAddr31..2 =
LLAddr31..2`; `Config5.LLB` does not exist in this profile), and it is `atomic_update` that
`StoreMemory` and the result `GPR[rt] ← 0^31 || LLbit` use. It is read before `StoreMemory`: the store
of the `SC` itself is not "between the LL and SC" (p.347), so the oracle choice that a store clears
`LLbit` (`Oracle.storeClearsLL`) does not apply to it; `LLbit ← 0` follows in any case. -/
def SC (base rt offset : W32) : Pseudo Unit := do
  -- vAddr ← sign_extend(offset) + GPR[base]
  let vAddr := sign_extend (imm9 offset) + (← GPR (reg base))
  -- if vAddr1..0 ≠ 0^2 then SignalException(AddressError) endif
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorStore vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, STORE)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .STORE
    -- dataword ← GPR[rt]
    let dataword ← GPR (reg rt)
    let a ← Pseudo.get
    -- atomic_update: LLbit, and the aligned address of the SC matches that of the LL (p.347)
    let atomic_update := a.LLbit && (bits vAddr 31 2 == bits a.LLAddr 31 2)
    -- if LLbit then StoreMemory (CCA, WORD, dataword, pAddr, vAddr, DATA) endif
    if atomic_update then StoreMemory CCA WORD dataword pAddr vAddr
    -- GPR[rt] ← 0^31 || LLbit
    setGPR (reg rt) ((0#31 ++ BitVec.ofBool atomic_update).setWidth 32)
    -- LLbit ← 0
    Pseudo.modify fun a => { a with LLbit := false }

end Manual.Ops

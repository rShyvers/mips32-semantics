import Semantics.Manual.Memory

/-!
# Manual.Ops.PcRel — the Release 6 PC-relative instructions (MD00086 Vol II-A Rev 6.06)

`ADDIUPC`, `AUIPC`, `ALUIPC` (address computation) and `LWPC` (load). PCREL opcode `111011`, minor
opcode in bits 20..16 (Table A.13, p.455).

`PC` is "the address of the instruction word" during its instruction time (MD00086 Vol II-A Rev 6.06
Table 1.1, p.6), in a delay slot too: these are not control transfer instructions, so a delay slot may
hold them (MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62, lists the instructions forbidden there). "Release
6 extends [memory_address] to ... the PC-relative address calculation instructions (ADDIUPC, AUIPC,
ALUIPC)" (§2.2.2.4.2, p.25), the identity on a 32-bit CPU. -/

namespace Manual.Ops

open Manual

/-- The 19-bit `immediate`/`offset` field of `ADDIUPC`/`LWPC` (bits 18..0). -/
def imm19 (w : W32) : BitVec 19 := w.extractLsb' 0 19

/-- **ADDIUPC rs, immediate** — MD00086 Vol II-A Rev 6.06, ADDIUPC, p.37.
```
GPR[rs] ← ( PC + sign_extend( immediate << 2 ) )
```
"The 19-bit immediate is shifted left by 2 bits, sign-extended, and added to the address of the
ADDIUPC instruction" (p.37): `immediate << 2` is the 21-bit string `immediate || 0^2`. -/
def ADDIUPC (rs imm : W32) : Pseudo Unit := do
  -- GPR[rs] ← ( PC + sign_extend( immediate << 2 ) )
  setGPR (reg rs) (memory_address ((← PC) + sign_extend (imm19 imm ++ 0#2)))

/-- **AUIPC rs, immediate** — MD00086 Vol II-A Rev 6.06, AUIPC, p.48.
```
GPR[rs] ← ( PC + ( immediate << 16 ) )
```
"The 16-bit immediate is shifted left by 16 bits, sign-extended, and added to the address of the AUIPC
instruction" (p.48): `immediate << 16` is the 32-bit string `immediate || 0^16`. -/
def AUIPC (rs imm : W32) : Pseudo Unit := do
  -- GPR[rs] ← ( PC + ( immediate << 16 ) )
  setGPR (reg rs) (memory_address ((← PC) + sign_extend (imm16 imm ++ 0#16)))

/-- **ALUIPC rs, immediate** — MD00086 Vol II-A Rev 6.06, ALUIPC, p.43.
```
GPR[rs] ← ~0x0FFFF & ( PC + sign_extend( immediate << 16 ) )
```
"The low 16 bits of the result are cleared, that is the result is aligned on a 64K boundary" (p.43). -/
def ALUIPC (rs imm : W32) : Pseudo Unit := do
  -- GPR[rs] ← ~0x0FFFF & ( PC + sign_extend( immediate << 16 ) )
  setGPR (reg rs) (~~~0x0FFFF#32 &&& memory_address ((← PC) + sign_extend (imm16 imm ++ 0#16)))

/-- **LWPC rs, offset** — MD00086 Vol II-A Rev 6.06, LWPC, p.246.
```
vAddr ← ( PC + sign_extend(offset)<<2)
(pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
GPR[rs] ← memword
```
Restrictions: "LWPC is naturally aligned, by specification" (p.246): `PC` is word-aligned (an
instruction fetch "not aligned on a word boundary" is an Address Error, MD00090 Vol III Rev 6.02
§6.2.9, p.92-93),
so `vAddr` is too. The alignment check of the other word loads (`Ops.LW`, the profile's Address Error
for every misaligned access) is transcribed all the same; it never fires. "The Release 6 PC-relative
loads (LWPC) are considered data references" (Programming Note, p.246): `DATA`. -/
def LWPC (rs offset : W32) : Pseudo Unit := do
  -- vAddr ← ( PC + sign_extend(offset)<<2)
  let vAddr := (← PC) + (sign_extend (imm19 offset) <<< 2)
  -- (alignment) misaligned: Address Error (load); never, `PC` is aligned
  if bits vAddr 1 0 != 0#2 then SignalException (.AddressErrorLoad vAddr)
  else
    -- (pAddr, CCA) ← AddressTranslation (vAddr, DATA, LOAD)
    let (pAddr, CCA) ← AddressTranslation vAddr .DATA .LOAD
    -- memword ← LoadMemory (CCA, WORD, pAddr, vAddr, DATA)
    let memword ← LoadMemory CCA WORD pAddr vAddr .DATA
    -- GPR[rs] ← memword
    setGPR (reg rs) memword

end Manual.Ops

import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Jump — jumps with a delay slot (MD00086 Vol II-A Rev 6.06)

7B S3. `I+1:` statements are scheduled with `I1` and happen in the next instruction time, whose `PC`
is the delay slot's address, `PC + 4` (§1.3, Table 1.1, p.6).

Release 6 has no separate JR/JR.HB: "Release 6: JR is defined to be JALR with the destination register
specifier rd set to 0 ... The pre-Release 6 instruction encoding for JR is removed in Release 6" (JR,
Availability and Compatibility, MD00086 Vol II-A Rev 6.06 p.207), so their words are the JALR/JALR.HB
diagrams. `JALR` has an `I+1:` arm for processors that implement MIPS16e or microMIPS
(`Config3ISA ≠ 0` or `Config1CA ≠ 0`); `ISAMode` is not a state of this profile (MIPS32 only), and `Config1.CA` (bit 2, MD00090 Vol III Rev 6.02, Table 9.65, p.240: "Code
compression (MIPS16e) implemented") is 0 in `Impl.Config1`; `Config3ISA` (bits 15..14, Table 9.67,
p.248: "0 Only MIPS32 Instruction Set is implemented") is 0, since `Impl.WF` requires `Config3 = 0`.
-/

namespace Manual.Ops

open Manual

/-- **J target** — MD00086 Vol II-A Rev 6.06, J, p.194.
```
I:
I+1: PC ← PC_{GPRLEN-1..28} || instr_index || 0^2
```
"The remaining upper bits are the corresponding bits of the address of the instruction in the delay
slot (not the branch itself)" (Description, p.194): in `I+1`, `PC` is that address. -/
def J (target : W32) : Pseudo Unit := do
  let pc ← PC
  -- I+1: PC ← PC_{GPRLEN-1..28} || instr_index || 0^2
  I1 (.jump ((bits (pc + 4#32) 31 28 ++ bits target 25 0 ++ 0#2 : BitVec 32)))

/-- **JAL target** — MD00086 Vol II-A Rev 6.06, JAL, p.195.
```
I:   GPR[31] ← PC + 8
I+1: PC ← PC_{GPRLEN-1..28} || instr_index || 0^2
```
-/
def JAL (target : W32) : Pseudo Unit := do
  let pc ← PC
  -- I: GPR[31] ← PC + 8
  setGPR 31 (pc + 8#32)
  -- I+1: PC ← PC_{GPRLEN-1..28} || instr_index || 0^2
  I1 (.jump ((bits (pc + 4#32) 31 28 ++ bits target 25 0 ++ 0#2 : BitVec 32)))

/-- **JALR rd, rs** — MD00086 Vol II-A Rev 6.06, JALR, p.196-197 (the Release 6 diagram has the same fields).
```
I:   temp ← GPR[rs]
     GPR[rd] ← PC + 8
I+1: if (Config3ISA = 0) and (Config1CA = 0) then
        PC ← temp
     else
        PC ← temp_{GPRLEN-1..1} || 0
        ISAMode ← temp_0
     endif
```
Restrictions (p.196): "Register specifiers rs and rd must not be equal ... The result of executing
such an instruction is UNPREDICTABLE" (`Oracle.jalrRsIsRd`). The `else` arm is not taken (`Config1.CA = 0`, module doc). -/
def JALR (rs rd : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  let body : Pseudo Unit := do
    -- I: temp ← GPR[rs]
    let temp ← GPR (reg rs)
    -- GPR[rd] ← PC + 8
    let pc ← PC
    setGPR (reg rd) (pc + 8#32)
    -- I+1: if (Config3ISA = 0) and (Config1CA = 0) then PC ← temp
    --      else PC ← temp_{GPRLEN-1..1} || 0 (ISAMode ← temp_0: not modelled)
    if !bit impl.Config1 2 then I1 (.jump temp)
    else I1 (.jump (bits temp 31 1 ++ 0#1 : BitVec 32))
  -- Restrictions: rs = rd is UNPREDICTABLE
  if reg rs == reg rd then unpredictableOr (o.jalrRsIsRd a (.jalr rs rd)) body else body

/-- **JALR.HB rd, rs** — MD00086 Vol II-A Rev 6.06, JALR.HB, p.198-199 (the Release 6 diagram has the same fields).
```
I: temp ← GPR[rs]
   GPR[rd] ← PC + 8
I+1:if (Config3ISA = 0) and (Config1CA = 0) then
       PC ← temp
    else
       PC ← temp_{GPRLEN-1..1} || 0
       ISAMode ← temp_0
    endif
    ClearHazards()
```
Restrictions (p.199): "Register specifiers rs and rd must not be equal ... The result of executing
such an instruction is UNPREDICTABLE" (`Oracle.jalrRsIsRd`). `ClearHazards()` has no architectural state. -/
def JALR_HB (rs rd : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  let body : Pseudo Unit := do
    -- I: temp ← GPR[rs]
    let temp ← GPR (reg rs)
    -- GPR[rd] ← PC + 8
    let pc ← PC
    setGPR (reg rd) (pc + 8#32)
    -- I+1: if (Config3ISA = 0) and (Config1CA = 0) then PC ← temp
    --      else PC ← temp_{GPRLEN-1..1} || 0 (ISAMode ← temp_0: not modelled)
    --      ClearHazards(): no state
    if !bit impl.Config1 2 then I1 (.jump temp)
    else I1 (.jump (bits temp 31 1 ++ 0#1 : BitVec 32))
  -- Restrictions: rs = rd is UNPREDICTABLE
  if reg rs == reg rd then unpredictableOr (o.jalrRsIsRd a (.jalrHb rs rd)) body else body

end Manual.Ops

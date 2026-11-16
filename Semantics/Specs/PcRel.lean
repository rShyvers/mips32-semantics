import Semantics.Specs.Tactics
import Semantics.Specs.DecodeSpec
import Semantics.Specs.Fixtures

/-!
# PcRel — the Release 6 PC-relative instructions

Constructors: `addiupc` `auipc` `aluipc` `lwpc`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page): ADDIUPC p.37; AUIPC p.48; ALUIPC p.43; LWPC
p.246. `PC` is the address of the instruction (Table 1.1, p.6): `s.pc`, in a delay slot too (these are
not control transfers, MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). The statements assume no pending
branch (`hpb`), as every `_spec_raw` theorem; in a delay slot the same value is written and the pending
target is committed (`mkNext`).

## Theorems in this file (4)

  `addiupc_spec_raw` `auipc_spec_raw` `aluipc_spec_raw` `lwpc_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`addiupc` writes `PC + sign_extend(immediate << 2)`** (ADDIUPC, p.37; `signExt19`, the 19-bit
immediate sign-extended). -/
theorem addiupc_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addiupc rs imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := s.pc + (signExt19 imm <<< 2)
      { (writeReg s (regIdxSpec rs) v) with pc := (writeReg s (regIdxSpec rs) v).pc + 4#32 }) := by
  step_spec

/-- **`auipc` writes `PC + (immediate << 16)`** (AUIPC, p.48). -/
theorem auipc_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.auipc rs imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := s.pc + (zeroExt16 imm <<< 16)
      { (writeReg s (regIdxSpec rs) v) with pc := (writeReg s (regIdxSpec rs) v).pc + 4#32 }) := by
  step_spec

/-- **`aluipc` writes `PC + (immediate << 16)` with the low 16 bits cleared** (ALUIPC, p.43). -/
theorem aluipc_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.aluipc rs imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := (s.pc + (zeroExt16 imm <<< 16)) &&& ~~~0xFFFF#32
      { (writeReg s (regIdxSpec rs) v) with pc := (writeReg s (regIdxSpec rs) v).pc + 4#32 }) := by
  step_spec

/-- **`lwpc` loads the word at `PC + sign_extend(offset) << 2`** (LWPC, p.246), or raises Address Error
for a misaligned address (never: `PC` is word-aligned when the instruction is fetched). -/
theorem lwpc_spec_raw (s : State) (w rs off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwpc rs off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := s.pc + (signExt19 off <<< 2)
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { (writeReg s (regIdxSpec rs) v) with pc := (writeReg s (regIdxSpec rs) v).pc + 4#32 }) := by
  step_spec

-- `addiupc` at `textBase` with immediate -1: `textBase - 4`; `lwpc` with offset 0 loads its own word.
#guard (let s := stepIn (prog1Spec (.addiupc 10#32 0x7ffff#32)) (initialState textBase)
        readReg s 10 == textBase - 4#32) = true
#guard (let s := stepIn (prog1Spec (.lwpc 10#32 0#32)) (initialState textBase)
        readReg s 10 == encode (.lwpc 10#32 0#32)) = true
#guard (let s := stepIn (prog1Spec (.aluipc 10#32 1#32)) (initialState textBase)
        readReg s 10 == 0x00410000#32) = true

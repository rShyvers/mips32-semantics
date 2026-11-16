import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Immediate — I-type immediate arithmetic and logic

Constructors: `addiu` `slti` `sltiu` `andi` `ori` `xori` `aui`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ADDIU p.36; SLTI p.379; SLTIU p.380; ANDI p.45-46; ORI p.315-316; XORI p.447; AUI p.47
  (LUI = AUI with rs = 0).

Reference: `docs/spec/INSTRUCTION-REF.md`, section "I-type immediate arithmetic / logic".

## Theorems in this file (8)

  `addiu_spec_raw` `slti_spec_raw` `sltiu_spec_raw` `andi_spec_raw` `ori_spec_raw` `xori_spec_raw`
  `aui_spec_raw` `aui_rs_zero_is_lui`
-/

set_option maxRecDepth 4000

/-! ## `addiu`, `slti`, `sltiu`, `andi`, `ori`, `xori`, `aui`

`docs/spec/INSTRUCTION-REF.md` "I-type immediate arithmetic / logic". None of these traps
(Release 6 removed ADDI); the statements differ in how the 16-bit immediate is extended (sign for
`addiu`/`slti`/`sltiu`, zero for `andi`/`ori`/`xori`, shifted into the upper half for `aui`). -/

/-- **`addiu` computes `$rs + sext16(imm)` with plain 32-bit wraparound and
never traps**: there is no overflow check at all (INSTRUCTION-REF "addiu" section; the trapping
ADDI was removed in Release 6). -/
theorem addiu_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addiu rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)).pc + 4#32 }) := by
  step_spec

/-- **`slti` writes `1` iff `$rs < sext16(imm)` under a signed comparison,
else `0`** (INSTRUCTION-REF "slti" section). -/
theorem slti_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.slti rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm)
               then 1#32 else 0#32
      { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  step_spec

/-- **`sltiu` sign-extends the 16-bit immediate first, exactly like `slti`,
then compares the resulting 32-bit values as unsigned** — the "u" affects
only the comparison, not the immediate's extension (INSTRUCTION-REF
"sltiu" section, same convention as this project's `sltu`; confirmed
against `Step.lean`'s `.sltiu` case, which calls `signExt16 imm` and then
compares `.toNat` values). -/
theorem sltiu_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sltiu rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat
               then 1#32 else 0#32
      { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  step_spec

/-- **`andi` zero-extends the 16-bit immediate, then bitwise-ANDs it with
`$rs`** — unlike `addiu`/`slti`, the immediate is zero-extended, not
sign-extended (INSTRUCTION-REF "andi" section: "immediate is
zero-extended... not sign-extended"). -/
theorem andi_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.andi rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)).pc + 4#32 }) := by
  step_spec

/-- **`ori` zero-extends the 16-bit immediate, then bitwise-ORs it with
`$rs`** (INSTRUCTION-REF "ori" section — same zero-extension convention as
`andi`). -/
theorem ori_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ori rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)).pc + 4#32 }) := by
  step_spec

/-- **`xori` zero-extends the 16-bit immediate, then bitwise-XORs it with
`$rs`** (INSTRUCTION-REF "xori" section — same zero-extension convention as
`andi`). -/
theorem xori_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.xori rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)).pc + 4#32 }) := by
  step_spec

/-- **`aui` adds `imm << 16` to `$rs` and writes the sum to `$rt`** (MD00086 Vol II-A Rev 6.06,
AUI, p.47: `GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)`; on 32 bits `sign_extend(imm << 16)`
is `zeroExt16 imm <<< 16`, the low 16 bits being zero). No overflow check. `lui` is `aui` with
`rs = 0` (`aui_rs_zero_is_lui`). -/
theorem aui_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.aui rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + (zeroExt16 imm <<< 16))) with
          pc := (writeReg s (regIdxSpec rt)
            (readReg s (regIdxSpec rs) + (zeroExt16 imm <<< 16))).pc + 4#32 }) := by
  step_spec

/-- **`lui $rt, imm` is `aui $rt, $zero, imm`** (MD00086 Vol II-A Rev 6.06, AUI, p.47; LUI is the
`rs = 0` case): with `$zero` reading 0 (an invariant of `step`, `step_preserves_zero_register`),
`$rt` receives `imm << 16`, the low half-word zero. -/
theorem aui_rs_zero_is_lui (s : State) (w rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.aui 0#32 rt imm))
    (hpb : s.pendingBranch = none) (hz : readReg s 0 = 0#32) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)) with
          pc := (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)).pc + 4#32 }) := by
  rw [aui_spec_raw s w 0#32 rt imm hfetch hdecode hpb hexec]
  have h0 : regIdxSpec 0#32 = (0 : Fin 32) := by decide
  rw [h0, hz, BitVec.zero_add]

-- `addiu_spec_raw`: `0x7fffffff + 1` wraps to `0x80000000` instead of trapping.
#guard (let s := stepIn (prog1Spec (.addiu 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32)])
        readReg s 9 == 0x80000000#32) = true

-- `slti_spec_raw`/`sltiu_spec_raw`: the same bit pattern (`-1` signed,
-- `0xffffffff` unsigned) compares differently against `0` depending on
-- signedness.
#guard (let s := stepIn (prog1Spec (.slti 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        readReg s 9 == 1#32) = true

#guard (let s := stepIn (prog1Spec (.sltiu 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        readReg s 9 == 0#32) = true

-- `andi_spec_raw`/`ori_spec_raw`/`xori_spec_raw`: the immediate is
-- zero-extended, not sign-extended — the high 16 bits of `$rs` are never
-- pulled from the immediate's sign.
#guard (let s := stepIn (prog1Spec (.andi 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        readReg s 9 == 0x00008001#32) = true

#guard (let s := stepIn (prog1Spec (.ori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)])
        readReg s 9 == 0x00008001#32) = true

#guard (let s := stepIn (prog1Spec (.xori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)])
        readReg s 9 == 0x00008001#32) = true

-- `aui_rs_zero_is_lui`: `lui $t1, 0x8001` (= `aui $t1, $zero, 0x8001`): the immediate lands in
-- the high half-word, the low half-word stays zero.
#guard (let s := stepIn (prog1Spec (.aui 0#32 9#32 0x8001#32)) (initialState textBase)
        readReg s 9 == 0x80010000#32) = true

-- `aui_spec_raw`: `$rs` is added (with wraparound): `0x8001_1234 + (0x8000 << 16)` = `0x0001_1234`.
#guard (let s := stepIn (prog1Spec (.aui 8#32 9#32 0x8000#32))
          (setRegsSpec (initialState textBase) [(8, 0x80011234#32)])
        readReg s 9 == 0x00011234#32) = true

import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Immediate — I-type immediate arithmetic and logic

Constructors: `addi` `addiu` `slti` `sltiu` `andi` `ori` `xori` `lui`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ADDI p.35; ADDIU p.36; SLTI p.379; SLTIU p.380; ANDI p.45-46; ORI p.315-316; XORI p.447;
  LUI p.233.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "I-type immediate arithmetic / logic".

## Theorems in this file (9)

  `addi_spec_raw` `addi_overflow_raises_ov` `addiu_spec_raw` `slti_spec_raw` `sltiu_spec_raw`
  `andi_spec_raw` `ori_spec_raw` `xori_spec_raw` `lui_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`addi` computes `$rs + sext16(imm)` exactly, or traps exactly on
signed overflow.** The immediate is sign-extended first (INSTRUCTION-REF
"addi" section), then the same overflow test as `add` applies. -/
theorem addi_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 }) := by
  step_spec

/-- **`addi` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem addi_overflow_raises_ov (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (signExt16 imm))
      (asSigned (readReg s (regIdxSpec rs) + signExt16 imm)) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) := by
  rw [step_of_executesInstr s hexec]; unfold execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show timerTick (if addOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-! ### Satisfiable examples -/

-- `addi_spec_raw`: `addi $t1, $zero, 5` does not overflow.
#guard (let s := stepIn (prog1Spec (.addi 0#32 9#32 5#32)) (initialState textBase)
        readReg s 9 == 5#32) = true

/-! ## `addiu`, `slti`, `sltiu`, `andi`, `ori`, `xori`, `lui`

`docs/spec/INSTRUCTION-REF.md` "I-type immediate arithmetic / logic". None of these traps;
the statements differ in how the 16-bit immediate is extended (sign for `addiu`/`slti`/`sltiu`,
zero for `andi`/`ori`/`xori`, shifted for `lui`). -/

/-- **`addiu` computes `$rs + sext16(imm)` with plain 32-bit wraparound and
never traps** — unlike `addi`, there is no overflow check at all (same
sign-extended immediate, but the "u" suffix removes the overflow test
entirely; INSTRUCTION-REF "addiu" section, confirmed against `Step.lean`'s
`.addiu` case, which has no `addOverflows`/exception branch whatsoever). -/
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
`$rs`** — unlike `addi`/`slti`, the immediate is zero-extended, not
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

/-- **`lui` writes `imm << 16` into `$rt`, ignoring `$rs` entirely** — `$rs`
is a fixed/unused field in the real encoding, and `Instruction.lui` itself
has no `rs` operand at all (INSTRUCTION-REF "lui" section: "$rt = imm <<
16", no sign extension needed since the low 16 bits are always discarded by
the shift). -/
theorem lui_spec_raw (s : State) (w rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lui rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)) with
          pc := (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)).pc + 4#32 }) := by
  step_spec

-- `addiu_spec_raw`: `0x7fffffff + 1` wraps to `0x80000000` instead of
-- trapping (the one observable difference from `addi`).
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

-- `lui_spec_raw`: the immediate lands in the high half-word, low half-word
-- stays zero, and `$rs` (here nonzero garbage) is ignored since `lui` has
-- no `rs` operand at all.
#guard (let s := stepIn (prog1Spec (.lui 9#32 0x8001#32)) (initialState textBase)
        readReg s 9 == 0x80010000#32) = true

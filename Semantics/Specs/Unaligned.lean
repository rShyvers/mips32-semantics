import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Unaligned — unaligned loads and stores (`lwl`/`lwr`/`swl`/`swr`)

Constructors: `lwl` `lwr` `swl` `swr`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  LWL p.240-242; LWR p.247-251; SWL p.397-398; SWR p.401-403.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Unaligned memory access (`lwl`/`lwr`/`swl`/`swr`) — v1.x addition".

## Theorems in this file (4)

  `lwl_spec_raw` `lwr_spec_raw` `swl_spec_raw` `swr_spec_raw`
-/

set_option maxRecDepth 4000

/-! ## `lwl`/`lwr`/`swl`/`swr`

`docs/spec/INSTRUCTION-REF.md` "Unaligned memory access" section. Unlike `lw`/`sw`, the effective
address has no alignment requirement: `readMemByte`/`writeMemByte` are total, so none of these
can raise Address Error (contrast `lw_spec_raw`), and `swl`/`swr`, like `sw`, clear `LLbit`.
Each right-hand side is `Step.lean`'s four-way match on `off := addr.toNat % 4`, written with
`setByteSlotSpec`/`getByteSlotSpec` (`Defs.lean`) and `readMemByte`/`writeMemByte`. -/

/-- **`lwl` ("load word left") merges 1–4 most-significant bytes starting at
`$rs + sext16(offset)` into the most-significant end of `$rt`, leaving
`$rt`'s existing least-significant bytes untouched** — exactly how many
bytes merge depends on `addr.toNat % 4` (4 at `off = 0`, behaving exactly
like a plain `lw`; down to 1 at `off = 3`). Never halts on a misaligned
address, unlike `lw` (INSTRUCTION-REF `lwl` section). -/
theorem lwl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let b0 := (readMemByte s addr).getD 0
      let v :=
        match off with
        | 0 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          let b3 := (readMemByte s (addr + 3#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
        | 1 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2
        | 2 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1
        | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
          setByteSlotSpec old 0 b0
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  step_spec

/-- **`lwr` ("load word right") merges 1–4 least-significant bytes ending
at `$rs + sext16(offset)` into the least-significant end of `$rt`, leaving
`$rt`'s existing most-significant bytes untouched** — the mirror image of
`lwl_spec_raw`: exactly how many bytes merge depends on `addr.toNat % 4`
(1 at `off = 0`, up to 4 at `off = 3`, behaving exactly like a plain `lw`).
Never halts on a misaligned address, unlike `lw` (INSTRUCTION-REF `lwr`
section). -/
theorem lwr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let v :=
        match off with
        | 0 =>
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec old 3 b3
        | 1 =>
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec old 2 b2) 3 b3
        | 2 =>
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 1 b1) 2 b2) 3 b3
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let b0 := (readMemByte s (addr - 3#32)).getD 0
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  step_spec

/-- **`swl` ("store word left") stores `$rt`'s most-significant 1–4 bytes
starting at `$rs + sext16(offset)`, and clears `llBit`** (store-class, like
`sw`/`sh`) — exactly how many bytes are stored depends on
`addr.toNat % 4` (4 at `off = 0`, behaving exactly like a plain `sw`; down
to 1 at `off = 3`). Never halts on a misaligned address, unlike `sw`
(INSTRUCTION-REF `swl` section). -/
theorem swl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s1 := (writeMemByte s addr (getByteSlotSpec v 0)).getD s
      let s' :=
        match off with
        | 0 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 (addr + 3#32) (getByteSlotSpec v 3)).getD s3
        | 1 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
        | 2 => (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
        | _ => s1  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  step_spec

/-- **`swr` ("store word right") stores `$rt`'s least-significant 1–4
bytes ending at `$rs + sext16(offset)`, and clears `llBit`** (store-class,
like `sw`/`sh`) — the mirror image of `swl_spec_raw`: exactly how many
bytes are stored depends on `addr.toNat % 4` (1 at `off = 0`, up to 4 at
`off = 3`, behaving exactly like a plain `sw`). Never halts on a misaligned
address, unlike `sw` (INSTRUCTION-REF `swr` section). -/
theorem swr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s' :=
        match off with
        | 0 => (writeMemByte s addr (getByteSlotSpec v 3)).getD s
        | 1 =>
          let s1 := (writeMemByte s (addr - 1#32) (getByteSlotSpec v 2)).getD s
          (writeMemByte s1 addr (getByteSlotSpec v 3)).getD s1
        | 2 =>
          let s1 := (writeMemByte s (addr - 2#32) (getByteSlotSpec v 1)).getD s
          let s2 := (writeMemByte s1 (addr - 1#32) (getByteSlotSpec v 2)).getD s1
          (writeMemByte s2 addr (getByteSlotSpec v 3)).getD s2
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let s1 := (writeMemByte s (addr - 3#32) (getByteSlotSpec v 0)).getD s
          let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr - 1#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 addr (getByteSlotSpec v 3)).getD s3
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  step_spec

/-- Base address for the concrete `lwl`/`lwr`/`swl`/`swr` examples below
(mirrors `Step.lean`'s test-only `unalignedBase`). -/
def unalignedBaseSpec : W32 := 0x10010000#32

/-- Write a list of `(address, byte)` pairs into `s.mem`, for building the
concrete unaligned-memory examples below (mirrors `setRegsSpec`'s `foldl`
shape; `writeMemByte` always succeeds — see its docstring — so the `.getD
acc` fallback is never actually exercised, same as every `.getD` in
`swl_spec_raw`/`swr_spec_raw` above). -/
def setMemBytesSpec (s : State) (kvs : List (W32 × UInt8)) : State :=
  kvs.foldl (fun acc kv => (writeMemByte acc kv.1 kv.2).getD acc) s

/-- Concrete state with `$t0` (register 8) pointing at `unalignedBaseSpec`
and bytes `0x11,0x22,...,0x88` at `unalignedBaseSpec + 0..7`, so every
byte-position merge `lwl`/`lwr` perform is individually visible in the
resulting word (mirrors `Step.lean`'s test-only `unalignedTestState`). -/
def unalignedTestStateSpec : State :=
  setMemBytesSpec (setRegsSpec (initialState textBase) [(8, unalignedBaseSpec)])
    [(unalignedBaseSpec + 0#32, 0x11), (unalignedBaseSpec + 1#32, 0x22),
     (unalignedBaseSpec + 2#32, 0x33), (unalignedBaseSpec + 3#32, 0x44),
     (unalignedBaseSpec + 4#32, 0x55), (unalignedBaseSpec + 5#32, 0x66),
     (unalignedBaseSpec + 6#32, 0x77), (unalignedBaseSpec + 7#32, 0x88)]

/-- Concrete state with `$t0` pointing at `unalignedBaseSpec` and `$t1`
holding `0xaabbccdd`, for the `swl`/`swr` examples below (mirrors
`Step.lean`'s test-only `swTestState`). -/
def swTestStateSpec : State :=
  setRegsSpec (initialState textBase) [(8, unalignedBaseSpec), (9, 0xaabbccdd#32)]

-- `lwl_spec_raw`: `off = 0` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwl 8#32 9#32 0#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwl_spec_raw`: the three misaligned offsets, `$rt`'s untouched low
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwl 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x000000ff#32)]) with
        | .next s => readReg s 9 == 0x223344ff#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.lwl 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x0000abcd#32)]) with
        | .next s => readReg s 9 == 0x3344abcd#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.lwl 8#32 9#32 3#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x00112233#32)]) with
        | .next s => readReg s 9 == 0x44112233#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: `off = 3` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwr 8#32 9#32 3#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: the three misaligned offsets, `$rt`'s untouched high
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwr 8#32 9#32 0#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabbcc00#32)]) with
        | .next s => readReg s 9 == 0xaabbcc11#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.lwr 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabb0000#32)]) with
        | .next s => readReg s 9 == 0xaabb1122#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.lwr 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaa000000#32)]) with
        | .next s => readReg s 9 == 0xaa112233#32
        | .halt _ => false) = true

-- Complementary-pair idiom: `lwl $rt, 1($rs)` then `lwr $rt, 4($rs)`
-- (addresses `A+1` and `A+4`, both unaligned/aligned-boundary-straddling)
-- together reconstruct the unaligned word spanning bytes `A+1..A+4`
-- (`0x22334455`), each byte supplied by exactly one of the two instructions.
-- Both instructions must come from the same two-instruction program (run
-- sequentially via its own advancing `pc`), not two independent
-- single-instruction programs both starting at `textBase`.
#guard (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32])
          unalignedTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32]) s1 with
            | .next s2 => readReg s2 9 == 0x22334455#32
            | .halt _ => false)
        | .halt _ => false) = true

-- `swl_spec_raw`: `off = 0` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swl 8#32 9#32 0#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swl_spec_raw`: the three misaligned offsets store only the top
-- `4 - off` bytes, starting at `addr`; bytes before `addr` (and after the
-- stored run) are untouched (read back as the zero-fill default).
#guard (match step (prog1Spec (.swl 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 1#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 4#32) == some 0
        | .halt _ => false) = true

#guard (match step (prog1Spec (.swl 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 2#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xbb
        | .halt _ => false) = true

#guard (match step (prog1Spec (.swl 8#32 9#32 3#32)) swTestStateSpec with
        | .next s => readMemByte s (unalignedBaseSpec + 3#32) == some 0xaa
        | .halt _ => false) = true

-- `swr_spec_raw`: `off = 3` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swr 8#32 9#32 3#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swr_spec_raw`: the three misaligned offsets store only the bottom
-- `off + 1` bytes, ending at `addr`.
#guard (match step (prog1Spec (.swr 8#32 9#32 0#32)) swTestStateSpec with
        | .next s => readMemByte s unalignedBaseSpec == some 0xdd
        | .halt _ => false) = true

#guard (match step (prog1Spec (.swr 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xdd
        | .halt _ => false) = true

#guard (match step (prog1Spec (.swr 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xdd
        | .halt _ => false) = true

-- Complementary-pair idiom: `swl $rt, 1($rs)` then `swr $rt, 4($rs)`
-- together store every byte of `$rt` into the unaligned word spanning
-- `A+1..A+4`, exactly once each. Same two-instruction-program caveat as
-- the `lwl`/`lwr` idiom example above.
#guard (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32])
          swTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32]) s1 with
            | .next s2 =>
              readMemByte s2 (unalignedBaseSpec + 1#32) == some 0xaa &&
                readMemByte s2 (unalignedBaseSpec + 2#32) == some 0xbb &&
                readMemByte s2 (unalignedBaseSpec + 3#32) == some 0xcc &&
                readMemByte s2 (unalignedBaseSpec + 4#32) == some 0xdd
            | .halt _ => false)
        | .halt _ => false) = true

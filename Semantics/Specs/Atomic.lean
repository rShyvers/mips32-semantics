import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Atomic — load-linked / store-conditional

Constructors: `ll` `sc`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  LL p.223-224; SC p.347-350.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Atomic synchronization (`ll`/`sc`) — v1.x addition".

## Theorems in this file (2)

  `ll_spec_raw` `sc_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`ll` loads a word exactly like `lw`, and additionally sets `llBit`
and records its effective address in `llAddr`** — the link state that a
later `sc` checks (INSTRUCTION-REF "ll" section; MD00086 Vol II-A Rev 6.06,
LL, p.223-224). It raises Address Error on a word-misaligned effective
address, exactly like `lw`. -/
theorem ll_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) := by
  step_spec

/-- **`sc` is conditional on `llBit` and on its address matching the
preceding `ll`'s, checked before `llBit` is cleared.** The effective address
is computed and alignment-checked unconditionally, just like `sw` (so a
misaligned `sc` raises Address Error regardless of `llBit`). Once the
address is valid: if `s.llBit` was `true` **and** the address equals
`s.llAddr` in bits 31..2, the aligned word ("An SC will fail if the aligned address of the SC does not match
that of the preceding LL" — MD00086 Vol II-A Rev 6.06, SC, p.347), the store
commits (`$rt`'s old value is written to memory) and `$rt` is overwritten
with `1` (success); otherwise the store does **not** commit and `$rt` is
overwritten with `0` (failure). Either way `llBit`
ends up `false`. This single theorem states both outcomes together
(mirroring how `beq_spec_raw` states taken/not-taken as one `if`), because
the whole point of `ll`/`sc` is this exact atomic-primitive contract, not
just "some memory operation happened" (INSTRUCTION-REF "sc" section). -/
theorem sc_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr >>> 2 == addr >>> 2 then
          { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 }) := by
  step_spec

-- `ll_spec_raw`: loads like `lw` and sets `llBit`.
#guard (match (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x2a#32).bind
          (fun s => some (stepIn (prog1Spec (.ll 8#32 9#32 0#32)) s)) with
        | some s => readReg s 9 == 0x2a#32 && s.llBit == true
        | _ => false) = true

-- `sc_spec_raw`, success case: `llBit` set means the store commits and
-- `$rt` becomes `1`.
#guard (let s := stepIn (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := true, llAddr := 0x10010000#32 }
        readReg s 9 == 1#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0x99#32) = true

-- `sc_spec_raw`, address mismatch: `llBit` is set but the preceding `ll` was
-- to another address, so the store does NOT commit and `$rt` becomes `0`.
#guard (let s := stepIn (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := true, llAddr := 0x10010004#32 }
        readReg s 9 == 0#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0#32) = true

-- `sc_spec_raw`, regression (Wave 7D model fix): the addresses are compared in bits 31..2 only
-- ("An SC will fail if the aligned address of the SC does not match that of the preceding LL",
-- MD00086 Vol II-A Rev 6.06, SC, p.347), so an `llAddr` of `0x8000_1001` and an `sc` to
-- `0x8000_1000` (the same aligned word) succeed. Before the fix the whole addresses were compared
-- and this `sc` failed.
#guard (let s := stepIn (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x80001000#32), (9, 0x99#32)]) with
            llBit := true, llAddr := 0x80001001#32 }
        readReg s 9 == 1#32 && s.llBit == false && readMemWord s 0x80001000#32 == some 0x99#32) = true

-- `sc_spec_raw`, failure case: `llBit` clear means the store does NOT
-- commit (memory stays `0`) and `$rt` becomes `0`.
#guard (let s := stepIn (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := false }
        readReg s 9 == 0#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0#32) = true

-- `sc_spec_raw`: a misaligned `sc` raises Address Error regardless of
-- `llBit` (the alignment check is unconditional).
#guard (let s' := stepIn (prog1Spec (.sc 8#32 9#32 1#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with llBit := true }
        s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr) = true

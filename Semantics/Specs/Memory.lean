import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Memory — aligned loads and stores, and the memory hints `sync`/`synci`/`pref`

Constructors: `lw` `sw` `lb` `lbu` `lh` `lhu` `sh` `sb` `sync` `synci` `pref`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  LW p.235; SW p.392; LB p.211; LBU p.213; LH p.219; LHU p.221; SH p.373; SB p.344-345;
  SYNC p.407-411; SYNCI p.412-414; PREF p.321-324.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Memory access"; "Memory-ordering / cache-hint instructions (`sync`/`synci`) — v1.x addition"; "Summary table".

## Theorems in this file (13)

  `lw_spec_raw` `lw_misaligned_spec` `lw_misaligned_no_load` `sw_spec_raw` `sh_spec_raw`
  `sb_spec_raw` `pref_spec_raw` `lb_spec_raw` `lbu_spec_raw` `lh_spec_raw` `lhu_spec_raw`
  `sync_spec_raw` `synci_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or raises Address Error on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  step_spec

/-- Corollary of `lw_spec_raw`: a misaligned effective address raises Address
Error, naming that exact address. -/
theorem lw_misaligned_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm) := by
  rw [lw_spec_raw p s w rs rt imm hfetch hdecode hpb]
  dsimp only
  rw [show readMemWord s (readReg s (regIdxSpec rs) + signExt16 imm) = none by
    unfold readMemWord
    rw [ite_of_pos hmisaligned]]

/-! ### Satisfiable examples -/

-- `lw_spec_raw`: a big-endian word loaded back out.
#guard (match
          (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
            0x10010000#32 0x12345678#32).bind
          (fun s => some (step (prog1Spec (.lw 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x12345678#32
        | _ => false) = true

-- `lw_misaligned_spec`: an unaligned effective address halts with the
-- exact failing address.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next s' => s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `lb_spec_raw`/`lbu_spec_raw`: the same high-bit byte sign-extends under `lb` and
-- zero-extends under `lbu`.
#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lb 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffffff80#32
        | _ => false) = true

#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lbu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00000080#32
        | _ => false) = true

/-! ### Bad-output rejection -/

/-- **A misaligned `lw` never loads.** A buggy implementation might round
the address down (or up) and load anyway; the real `lw` raises Address
Error (AdEL) on a misaligned effective address: the step is exactly
exception entry with `BadVAddr` = that address, and no general register —
in particular `$rt` — is written. -/
theorem lw_misaligned_no_load (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    ∃ s', step p s = StepResult.next s' ∧ s'.regs = s.regs ∧
      s'.cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm := by
  rw [lw_misaligned_spec p s w rs rt imm hfetch hdecode hpb hmisaligned]
  exact ⟨_, rfl, rfl, rfl⟩

-- Concrete witness: `lw` from a `+1`-misaligned address raises AdEL with
-- `BadVAddr` = the address; `$9` is not written.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x55#32)]) with
        | .next s' => causeExcCode s' == excCodeAdEL && s'.cp0BadVAddr == 0x10010001#32
            && readReg s' 9 == 0x55#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## `sw`, `sh`, `sb`, `lb`, `lbu`, `lh`, `lhu`

Like `lw`: each statement restates its `step` case with the public memory primitives
(`readMemHalf`/`writeMemWord`/`writeMemHalf`, …) and raises Address Error on a misaligned
effective address where the access has an alignment requirement. (`ll`/`sc` are in `Atomic.lean`,
`lwl`/`lwr`/`swl`/`swr` in `Unaligned.lean`.) -/

/-- **`sw` stores `$rt` as a big-endian word at `$rs + sext16(offset)` and
clears `llBit`** (any store invalidates a pending `ll`/`sc` pair, so a
subsequent `sc` correctly fails if memory changed underneath it), or raises
Address Error on a misaligned effective address (INSTRUCTION-REF "sw"
section). -/
theorem sw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  step_spec

/-- **`sh` stores the low 16 bits of `$rt` as a big-endian halfword at
`$rs + sext16(offset)` and clears `llBit`**, or raises Address Error
on a halfword-misaligned effective address (INSTRUCTION-REF "sh" section).
-/
theorem sh_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemHalf s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  step_spec

/-- **`sb` stores the low byte of `$rt` at `$rs + sext16(offset)` and
clears `llBit`** (MD00086 "SB": `StoreMemory(BYTE, GPR[rt] 7..0)`). There is
no alignment requirement, so `sb` never raises an Address Error; exactly
one memory byte changes. Clearing `llBit` is the model's pinned choice for
every store (see `State.llBit`). -/
theorem sb_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with
            mem := s.mem.insert (readReg s (regIdxSpec rs) + signExt16 imm)
              (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
            llBit := false
            pc := s.pc + 4#32 } := by
  step_spec

-- `sb_spec_raw`: `sb $9, 1($8)` writes exactly the low byte `0xab` at the
-- (odd) address, leaves its neighbours alone, and clears `llBit`.
#guard (match step (prog1Spec (.sb 8#32 9#32 1#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x123456ab#32)]) with llBit := true } with
        | .next s => readMemByte s 0x10010001#32 == some 0xab && readMemByte s 0x10010000#32 == some 0
            && readMemByte s 0x10010002#32 == some 0 && s.llBit == false && s.pc == textBase + 4#32
        | .halt _ => false) = true

-- the assembled word `0xa1090001` is `sb $9, 1($8)`.
example : decode 0xa1090001#32 = some (.sb 8#32 9#32 1#32) := by decide

-- `sw_spec_raw`: a stored word reads back exactly, and clears a
-- previously-set `llBit`.
#guard (match step (prog1Spec (.sw 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x12345678#32)]) with
            llBit := true } with
        | .next s => readMemWord s 0x10010000#32 == some 0x12345678#32 && s.llBit == false
        | .halt _ => false) = true

-- `sw_spec_raw`: a misaligned `sw` raises Address Error, it never
-- rounds the address and stores anyway.
#guard (match step (prog1Spec (.sw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next s' => s'.cp0BadVAddr == 0x10010001#32 && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `lh_spec_raw`/`lhu_spec_raw`: the same high-bit halfword sign-extends under `lh`
-- and zero-extends under `lhu`.
#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lh 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffff8001#32
        | _ => false) = true

#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lhu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00008001#32
        | _ => false) = true

-- `sh_spec_raw`: only the low 16 bits of `$rt` are stored, and `llBit` is
-- cleared.
#guard (match step (prog1Spec (.sh 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0xffff1234#32)]) with
            llBit := true } with
        | .next s => readMemHalf s 0x10010000#32 == some 0x00001234#32 && s.llBit == false
        | .halt _ => false) = true

/-- **`pref` is a no-op**: "Any action, including doing nothing, is
permitted … PREF does not cause addressing-related exceptions" (MD00086
Vol II-A Rev 6.06, PREF, p.321). Only `pc` changes; it never raises, whatever
the address and hint. -/
theorem pref_spec_raw (p : Program) (s : State) (w rs hint imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.pref rs hint imm))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`lb` sign-extends the loaded byte** (INSTRUCTION-REF "lb" section).
`readMemByte` never fails, so the `none` arm is unreachable; it is kept so
the equation matches `step`'s code. -/
theorem lb_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)) with
            pc := (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)).pc + 4#32 } := by
  step_spec

/-- **`lbu` zero-extends the loaded byte** — same address and byte as `lb`, different widening (INSTRUCTION-REF "lbu" section). -/
theorem lbu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lbu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)) with
            pc := (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)).pc + 4#32 } := by
  step_spec

/-- **`lh` sign-extends the loaded big-endian halfword**, or raises Address Error (AdEL) on an odd address (INSTRUCTION-REF "lh" section). -/
theorem lh_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (signExt16 h)) with
            pc := (writeReg s (regIdxSpec rt) (signExt16 h)).pc + 4#32 } := by
  step_spec

/-- **`lhu` zero-extends the loaded big-endian halfword**, or raises Address Error (AdEL) on an odd address (INSTRUCTION-REF "lhu" section). -/
theorem lhu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lhu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) h) with
            pc := (writeReg s (regIdxSpec rt) h).pc + 4#32 } := by
  step_spec

/-! ## `sync`/`synci`

No-ops in this model (`Step.lean`): only `pc` advances. -/

/-- **`sync` is a documented no-op**: this single-hart simulator models no
concurrency or out-of-order execution for a memory-ordering barrier to
order anything against, so `sync` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `sync` docstring: `mkNext s s`). -/
theorem sync_spec_raw (p : Program) (s : State) (w stype : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sync stype))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`synci` is a documented no-op**: it computes the same effective
address as `lw`/`sw` (`readReg s rs + signExt16 offset`) for architectural
fidelity, but this simulator has no instruction-cache model to flush, so
the address is immediately discarded and `synci` falls through to `pc + 4`
touching no other state at all, not even a memory read (`Step.lean`'s
`synci` docstring). -/
theorem synci_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.synci rs imm))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

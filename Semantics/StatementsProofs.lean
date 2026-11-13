import Semantics.Specs.StepSpec

/-!
# StatementsProofs — the solution module for `lake comparator`

For every theorem of `Semantics/Statements.lean` (the statements-only challenge), in the same
order: the same statement, proved by the real theorem of the same name from `Semantics/Specs/`.
Nothing is proved here that is not already proved there; this file only makes the two sides
comparable (see `docs/PROOF-NOTES.md`, "The comparator arrangement"). `Checked.lean` imports it,
so `lake check` kernel-replays these one-line proofs too.

A statement edited here but not in `Statements.lean` (or vice versa) makes `lake comparator` fail;
a statement here that the cited theorem does not prove makes the build fail.
-/

set_option maxRecDepth 4000

namespace Trusted

/-! ## Decode / encode -/

theorem decode_encode (i : Instruction) (h : i.WellFormed) : decode (encode i) = some i :=
  _root_.decode_encode i h

/-! ## Global invariants -/

theorem step_preserves_zero_register (s : State) : readReg (step s) 0 = readReg s 0 :=
  _root_.step_preserves_zero_register s

theorem run_preserves_zero_register (s₀ : State) (n : Nat) :
    readReg (run s₀ n) 0 = readReg s₀ 0 :=
  _root_.run_preserves_zero_register s₀ n

theorem run_initialState_zero_register (pc : W32) (n : Nat) :
    readReg (run (initialState pc) n) 0 = 0#32 :=
  _root_.run_initialState_zero_register pc n

theorem zero_write_not_observable (s : State) (v : W32) (hv : readReg s 0 ≠ v) :
    readReg (writeReg s 0 v) 0 ≠ v :=
  _root_.zero_write_not_observable s v hv

theorem step_preserves_wellFormed (s : State) (hwf : s.RegFilesWF) : (step s).RegFilesWF :=
  _root_.step_preserves_wellFormed s hwf

theorem run_initialState_wellFormed (pc : W32) (n : Nat) :
    (run (initialState pc) n).RegFilesWF :=
  _root_.run_initialState_wellFormed pc n

/-! ## Exception entry -/

theorem exceptionEntry_always (s : State) (code ce : W32) :
    (exceptionEntry s code ce).pc =
        (if s.cp0Status &&& statusBevMask == 0#32 then
          ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x180#32
         else 0xBFC00380#32) ∧
      (exceptionEntry s code ce).cp0Status = s.cp0Status ||| statusExlMask ∧
      (exceptionEntry s code ce).pendingBranch = none ∧
      (exceptionEntry s code ce).regs = s.regs ∧
      (exceptionEntry s code ce).hi = s.hi ∧ (exceptionEntry s code ce).lo = s.lo ∧
      (exceptionEntry s code ce).mem = s.mem ∧
      (exceptionEntry s code ce).fpRegs = s.fpRegs ∧
      (exceptionEntry s code ce).fcsr = s.fcsr ∧
      (exceptionEntry s code ce).llBit = false ∧
      (exceptionEntry s code ce).cp0BadVAddr = s.cp0BadVAddr ∧
      (exceptionEntry s code ce).cp0ErrorEpc = s.cp0ErrorEpc ∧
      (exceptionEntry s code ce).cp0EBase = s.cp0EBase ∧
      (exceptionEntry s code ce).llAddr = s.llAddr :=
  _root_.exceptionEntry_always s code ce

theorem exceptionEntry_exl0_not_in_delay_slot (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = none) :
    (exceptionEntry s code ce).cp0Epc = s.pc ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) :=
  _root_.exceptionEntry_exl0_not_in_delay_slot s code ce hexl hpb

theorem exceptionEntry_exl0_in_delay_slot (s : State) (code ce t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (exceptionEntry s code ce).cp0Epc = s.pc - 4#32 ∧
      (exceptionEntry s code ce).cp0Cause =
        (((s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) :=
  _root_.exceptionEntry_exl0_in_delay_slot s code ce t hexl hpb

theorem exceptionEntry_exl1 (s : State) (code ce : W32)
    (hexl : s.cp0Status &&& statusExlMask ≠ 0#32) :
    (exceptionEntry s code ce).cp0Epc = s.cp0Epc ∧
      (exceptionEntry s code ce).cp0Cause =
        ((s.cp0Cause &&& ~~~(causeExcCodeMask ||| causeCeMask))
          ||| ((code <<< 2) &&& causeExcCodeMask)) ||| ((ce <<< 28) &&& causeCeMask) :=
  _root_.exceptionEntry_exl1 s code ce hexl

theorem exceptionEntry_excCode (s : State) (code ce : W32) :
    causeExcCode (exceptionEntry s code ce) = code &&& 31#32 :=
  _root_.exceptionEntry_excCode s code ce

/-! ## Fetch and decode failures -/

theorem step_misaligned_pc (s : State) (h : s.pc.toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdEL s.pc :=
  _root_.step_misaligned_pc s h

theorem step_fetches_from_memory (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr) :
    step s = execInstr s instr :=
  _root_.step_fetches_from_memory s w instr hfetch hdecode

theorem step_undecodable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none) :
    step s =
      if isCop1Word w && !cu1Enabled s then (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI :=
  _root_.step_undecodable s w hfetch hdecode

theorem step_reserved_instruction (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) :
    step s = takeException s excCodeRI :=
  _root_.step_reserved_instruction s w hfetch hdecode hc1 hc2

/-! ## Delay slots -/

theorem delay_slot_commits_target (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step { s with pendingBranch := none } = s')
    (hnormal : s'.pc = s.pc + 4#32) :
    step { s with pendingBranch := some t } = { s' with pc := t } :=
  _root_.delay_slot_commits_target s t w instr s' hfetch hdecode hnb hvec h0 hnormal

theorem branch_in_delay_slot_reserved_instruction (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) :
    step s = takeException s excCodeRI :=
  _root_.branch_in_delay_slot_reserved_instruction s w instr hfetch hdecode hpb hbr

/-! ## R-type arithmetic -/

theorem add_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) :
    step s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } :=
  _root_.add_spec_raw s w rs rt rd hfetch hdecode hpb

theorem sub_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) :
    step s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } :=
  _root_.sub_spec_raw s w rs rt rd hfetch hdecode hpb

theorem add_overflow_raises_ov (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) :
    step s = takeException s excCodeOv :=
  _root_.add_overflow_raises_ov s w rs rt rd hfetch hdecode hov

theorem add_overflow_not_wrapped (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) :
    step s = (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs :=
  _root_.add_overflow_not_wrapped s w hfetch hdecode hpb ha hb

/-! ## Immediates -/

theorem addi_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 } :=
  _root_.addi_spec_raw s w rs rt imm hfetch hdecode hpb

theorem addi_overflow_raises_ov (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (signExt16 imm))
      (asSigned (readReg s (regIdxSpec rs) + signExt16 imm)) = true) :
    step s = takeException s excCodeOv :=
  _root_.addi_overflow_raises_ov s w rs rt imm hfetch hdecode hov

/-! ## Shifts -/

theorem sll_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 } :=
  _root_.sll_spec_raw s w rd rt shamt hfetch hdecode hpb

/-! ## Multiply / divide -/

theorem mult_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) :
    step s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } :=
  _root_.mult_spec_raw s w rs rt hfetch hdecode hpb

theorem div_spec_raw (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) :
    step s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        { s with pc := s.pc + 4#32 }
      else
        { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 } :=
  _root_.div_spec_raw s w rs rt hfetch hdecode hpb

theorem div_by_zero_spec (s : State) (w rs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step s = { s with pc := s.pc + 4#32 } :=
  _root_.div_by_zero_spec s w rs rt hfetch hdecode hpb hzero

/-! ## Bit operations -/

theorem ext_spec_raw (s : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step s =
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 } :=
  _root_.ext_spec_raw s w rt rs pos size hfetch hdecode hpb

/-! ## Loads and stores -/

theorem lw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } :=
  _root_.lw_spec_raw s w rs rt imm hfetch hdecode hpb

theorem lw_misaligned_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm) :=
  _root_.lw_misaligned_spec s w rs rt imm hfetch hdecode hpb hmisaligned

theorem sw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } :=
  _root_.sw_spec_raw s w rs rt imm hfetch hdecode hpb

theorem sb_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      { s with
            mem := s.mem.insert (readReg s (regIdxSpec rs) + signExt16 imm)
              (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
            llBit := false
            pc := s.pc + 4#32 } :=
  _root_.sb_spec_raw s w rs rt imm hfetch hdecode hpb

theorem ll_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } :=
  _root_.ll_spec_raw s w rs rt imm hfetch hdecode hpb

theorem sc_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr == addr then
          { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 } :=
  _root_.sc_spec_raw s w rs rt imm hfetch hdecode hpb

theorem lwl_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
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
      { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } :=
  _root_.lwl_spec_raw s w rs rt imm hfetch hdecode hpb

/-! ## Branches and jumps -/

theorem beq_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } :=
  _root_.beq_spec_raw s w rs rt imm hfetch hdecode hpb

theorem beq_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } :=
  _root_.beq_taken_spec s w rs rt imm hfetch hdecode hpb htaken

theorem beql_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } :=
  _root_.beql_spec_raw s w rs rt imm hfetch hdecode hpb

theorem beql_not_taken_squashes_delay_slot (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 8#32 } ∧
      run s 1 = { s with pc := s.pc + 8#32 } :=
  _root_.beql_not_taken_squashes_delay_slot s w rs rt imm hfetch hdecode hpb hnot

theorem j_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } :=
  _root_.j_spec_raw s w target hfetch hdecode hpb

theorem jal_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } :=
  _root_.jal_spec_raw s w target hfetch hdecode hpb

theorem jal_sets_ra (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 :=
  _root_.jal_sets_ra s w target hfetch hdecode hpb hsize32

theorem jalr_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) } :=
  _root_.jalr_spec_raw s w rs rd hfetch hdecode hpb

/-! ## Traps, `break`, `syscall` -/

theorem teq_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 } :=
  _root_.teq_spec_raw s w rs rt code hfetch hdecode hpb

theorem break_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.break code)) :
    step s = takeException s excCodeBp :=
  _root_.break_spec_raw s w code hfetch hdecode

theorem syscall_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.syscall code)) :
    step s = takeException s excCodeSys :=
  _root_.syscall_spec_raw s w code hfetch hdecode

/-! ## Coprocessor 0 -/

theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step s =
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 8, 0 => read s.cp0BadVAddr
      | 12, 0 => read s.cp0Status
      | 13, 0 => read s.cp0Cause
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read 0x80008402#32
      | 16, 1 => read 0x00000001#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI :=
  _root_.mfc0_spec_raw s w rt rd sel hfetch hdecode hpb

theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step s =
      match rd.toNat, sel.toNat with
      | 8, 0 => { s with pc := s.pc + 4#32 }
      | 12, 0 =>
        { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 => { s with pc := s.pc + 4#32 }
      | 16, 1 => { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI :=
  _root_.mtc0_spec_raw s w rt rd sel hfetch hdecode hpb

theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step s =
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false } :=
  _root_.eret_spec_raw s w hfetch hdecode hpb

/-! ## Floating point -/

theorem fp_coprocessor_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop1 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cu1Enabled s = false) :
    step s = takeCoprocessorUnusable s :=
  _root_.fp_coprocessor_unusable s w instr hfetch hdecode huses hnb hcu

theorem fpCompletesS_trap (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesS s fd r = s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.mem = s.mem ∧ s'.pc = exceptionVector s :=
  _root_.fpCompletesS_trap s s' fd r hen h

theorem fpCompletesS_ok (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false) (hsize : s.fpRegs.size = 32)
    (h : fpCompletesS s fd r = s') :
    readFpReg s' (regIdx fd) = r.1 ∧ s'.fcsr = Mips.Fp.raiseFlags s.fcsr r.2 ∧
      s'.pc = s.pc + 4#32 ∧ s'.regs = s.regs :=
  _root_.fpCompletesS_ok s s' fd r hen hsize h

theorem addS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) :=
  _root_.addS_spec_raw s w fd fs ft hfetch hdecode hpb hcu

theorem addD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft)) :=
  _root_.addD_spec_raw s w fd fs ft hfetch hdecode hpb hcu

theorem cvtWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs))) :=
  _root_.cvtWS_spec_raw s w fd fs hfetch hdecode hpb hcu

theorem cCondS_spec_raw (s : State) (w cond cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS cond cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      fpCompletesCmp s cc
        (Mips.Fp.f32Compare (cond.setWidth 4) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) :=
  _root_.cCondS_spec_raw s w cond cc fs ft hfetch hdecode hpb hcu

theorem c_lt_s_sets_cc (s s' : State) (w cc fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cCondS 12#32 cc fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hen : Mips.Fp.fpeEnabled s.fcsr (Mips.Fp.f32Compare Mips.Fp.Cond.lt
      (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2 = false)
    (hstep : step s = s') :
    Mips.Fp.getCC s'.fcsr (ccIdx cc) = true ↔
      Mips.Fp.F32Lt (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)) :=
  _root_.c_lt_s_sets_cc s s' w cc fs ft hfetch hdecode hpb hcu hen hstep

theorem movf_spec_raw (s : State) (w rs cc rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movf rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then { s with pc := s.pc + 4#32 }
      else
        { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 } :=
  _root_.movf_spec_raw s w rs cc rd hfetch hdecode hpb hcu

theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 } :=
  _root_.mfc1_spec_raw s w rt fs hfetch hdecode hpb hcu

theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 } :=
  _root_.lwc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu

theorem lwc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm) :=
  _root_.lwc1_misaligned_spec s w rs ft imm hfetch hdecode hpb hcu hmisaligned

theorem cfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      { (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) with pc := (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)).pc + 4#32 } :=
  _root_.cfc1_spec_raw s w rt fs hfetch hdecode hpb hcu

theorem ctc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none => { s with pc := s.pc + 4#32 }
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else { s with fcsr := f, pc := s.pc + 4#32 } :=
  _root_.ctc1_spec_raw s w rt fs hfetch hdecode hpb hcu

theorem fcsr_ctc1_cfc1_roundtrip (fcsr v : W32) :
    ∃ f, Mips.Fp.writeControl fcsr 31 v = some f ∧ f = v &&& Mips.Fp.fcsrWritableMask ∧
      Mips.Fp.readControl f 31 = some (v &&& Mips.Fp.fcsrWritableMask) :=
  _root_.fcsr_ctc1_cfc1_roundtrip fcsr v

theorem bc1t_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1t cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } :=
  _root_.bc1t_spec_raw s w cc imm hfetch hdecode hpb hcu

/-! ## Self-modifying code and the hosted environment -/

theorem sw_next_instruction_is_fetched (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32) :
    (step s).pc = s.pc + 4#32 ∧
      readMemWord (step s) (step s).pc = some (readReg s (regIdxSpec rt)) :=
  _root_.sw_next_instruction_is_fetched s w rs rt imm hfetch hdecode hpb haddr

theorem store_changes_next_instruction (s : State) (w rs rt imm : W32) (instr' : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hnew : decode (readReg s (regIdxSpec rt)) = some instr') :
    step (step s) = execInstr (step s) instr' :=
  _root_.store_changes_next_instruction s w rs rt imm instr' hfetch hdecode hpb haddr hnew

theorem hostStep_eq_step (env : HostEnv) (h : Hosted)
    (hstop : stopReason env h.machine = none)
    (hsvc : env.services = false ∨ selectedService h.machine = none) :
    hostStep env h = .next { h with machine := step h.machine } :=
  _root_.hostStep_eq_step env h hstop hsvc

theorem runHosted_agrees_with_run (env : HostEnv) (out : String) (n : Nat) (s : State)
    (hquiet : ∀ j, j < n → stopReason env (run s j) = none ∧
      (env.services = false ∨ selectedService (run s j) = none)) :
    runHosted env n { machine := s, out := out } = .limitReached { machine := run s n, out := out } n :=
  _root_.runHosted_agrees_with_run env out n s hquiet

theorem hosted_print_int (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 1#32)
    (hpb : h.machine.pendingBranch = none) :
    hostStep env h =
      .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
              out := h.out ++ toString (asSigned (readReg h.machine (regIdxSpec 4#32))) } :=
  _root_.hosted_print_int env h w code hstop hon hfetch hdecode hv0 hpb

theorem hosted_exit (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 10#32) :
    hostStep env h = .halt .exit :=
  _root_.hosted_exit env h w code hstop hon hfetch hdecode hv0

theorem runHosted_preserves_zero_register (env : HostEnv) (n : Nat) (h : Hosted) :
    readReg (runHosted env n h).final.machine 0 = readReg h.machine 0 :=
  _root_.runHosted_preserves_zero_register env n h

end Trusted

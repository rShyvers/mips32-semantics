import Semantics.Specs.StepSpec
import Semantics.Refine.Determinism
import Semantics.Refine.ChoiceExact
import Semantics.Refine.ImplValid
import Semantics.FpOpsCorrectApi
import Semantics.FpOpsCorrectIEEE
import Semantics.FpOpsCorrectFma
import Semantics.FpOpsCorrectR6

/-!
# StatementsProofs — the solution module for `lake comparator`

For every theorem of `Semantics/Statements.lean` (the statements-only challenge), in the same
order: the same statement, proved by the real theorem of the same name from `Semantics/Specs/`
(the last section: from `Semantics/Refine/`, namespace `Refine`).
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
      (exceptionEntry s code ce).physMem = s.physMem ∧
      (exceptionEntry s code ce).fpRegs = s.fpRegs ∧
      (exceptionEntry s code ce).fcsr = s.fcsr ∧
      (exceptionEntry s code ce).llBit = s.llBit ∧
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

theorem step_misaligned_pc (s : State) (h : s.pc.toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL s.pc) :=
  _root_.step_misaligned_pc s h hexec

theorem step_fetches_from_memory (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr) (hexec : executesInstr s = true) :
    step s = timerTick (execInstr s instr) :=
  _root_.step_fetches_from_memory s w instr hfetch hdecode hexec

theorem step_undecodable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if isCop0Word w && !cp0Usable s then (exceptionEntry s excCodeCpU 0#32)
      else if isCop1Word w && !cu1Enabled s then (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI) :=
  _root_.step_undecodable s w hfetch hdecode hexec

theorem step_reserved_instruction (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc0 : isCop0Word w = false ∨ cp0Usable s = true)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.step_reserved_instruction s w hfetch hdecode hc0 hc1 hc2 hexec

theorem step_reserved_cop0_unusable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc0 : isCop0Word w = true) (hcu : cp0Usable s = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeCop0Unusable s) :=
  _root_.step_reserved_cop0_unusable s w hfetch hdecode hc0 hcu hexec

/-! ## Delay slots -/

theorem delay_slot_commits_target (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step { s with pendingBranch := none } = s')
    (hnormal : s'.pc = s.pc + 4#32) (hexec : executesInstr s = true) :
    step { s with pendingBranch := some t } = { s' with pc := t } :=
  _root_.delay_slot_commits_target s t w instr s' hfetch hdecode hnb hvec h0 hnormal hexec

theorem branch_in_delay_slot_reserved_instruction (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.branch_in_delay_slot_reserved_instruction s w instr hfetch hdecode hpb hbr hexec

theorem beqc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) :=
  _root_.beqc_spec_raw s w rs rt off hfetch hdecode hpb hexec

theorem forbidden_slot_cti_reserved (s : State) (w w2 rs rt off : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt))
    (hfetch2 : readMemWord (step s) (step s).pc = some w2) (hdecode2 : decode w2 = some instr)
    (hcti : isBranchLikeSpec instr = true) (hexec2 : executesInstr (step s) = true) :
    step (step s) = timerTick (takeException (step s) excCodeRI) :=
  _root_.forbidden_slot_cti_reserved s w w2 rs rt off instr hfetch hdecode hpb hexec hnot hfetch2
    hdecode2 hcti hexec2

/-! ## R-type arithmetic -/

theorem add_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 }) :=
  _root_.add_spec_raw s w rs rt rd hfetch hdecode hpb hexec

theorem sub_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 }) :=
  _root_.sub_spec_raw s w rs rt rd hfetch hdecode hpb hexec

theorem add_overflow_raises_ov (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) :=
  _root_.add_overflow_raises_ov s w rs rt rd hfetch hdecode hov hexec

theorem add_overflow_not_wrapped (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs :=
  _root_.add_overflow_not_wrapped s w hfetch hdecode hpb ha hb hexec

/-! ## Shifts -/

theorem sll_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 }) :=
  _root_.sll_spec_raw s w rd rt shamt hfetch hdecode hpb hexec

/-! ## Bit operations -/

theorem ext_spec_raw (s : State) (w rt rs pos size : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 }) :=
  _root_.ext_spec_raw s w rt rs pos size hfetch hdecode hpb hexec

/-! ## Loads and stores -/

theorem lw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) :=
  _root_.lw_spec_raw s w rs rt imm hfetch hdecode hpb hexec

theorem lw_misaligned_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) :=
  _root_.lw_misaligned_spec s w rs rt imm hfetch hdecode hpb hmisaligned hexec

theorem sw_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' =>
        { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 }) :=
  _root_.sw_spec_raw s w rs rt imm hfetch hdecode hpb hexec

theorem sb_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sb rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      match translate s (readReg s (regIdxSpec rs) + signExt16 imm) with
      | none => takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)
      | some pa =>
        { s with
              physMem := s.physMem.insert pa (readReg s (regIdxSpec rt) &&& 0xff#32).toNat.toUInt8
              llBit := false
              pc := s.pc + 4#32 }) :=
  _root_.sb_spec_raw s w rs rt imm hfetch hdecode hpb hexec

theorem ll_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt9 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v =>
        { ({ (writeReg s (regIdxSpec rt) v) with llBit := true, llAddr := addr }) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }) :=
  _root_.ll_spec_raw s w rs rt imm hfetch hdecode hpb hexec

theorem sc_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdxSpec rs) + signExt9 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => takeAddressException s excCodeAdES addr
      | some stored =>
        if s.llBit && s.llAddr >>> 2 == addr >>> 2 then
          { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 }) :=
  _root_.sc_spec_raw s w rs rt imm hfetch hdecode hpb hexec

/-! ## Branches and jumps -/

theorem beq_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) :=
  _root_.beq_spec_raw s w rs rt imm hfetch hdecode hpb hexec

theorem beq_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }) :=
  _root_.beq_taken_spec s w rs rt imm hfetch hdecode hpb htaken hexec

theorem j_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) :=
  _root_.j_spec_raw s w target hfetch hdecode hpb hexec

theorem jal_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) :=
  _root_.jal_spec_raw s w target hfetch hdecode hpb hexec

theorem jal_sets_ra (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 :=
  _root_.jal_sets_ra s w target hfetch hdecode hpb hsize32 hexec

theorem jalr_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) }) :=
  _root_.jalr_spec_raw s w rs rd hfetch hdecode hpb hexec

/-! ## Traps, `break`, `syscall` -/

theorem teq_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) :=
  _root_.teq_spec_raw s w rs rt code hfetch hdecode hpb hexec

theorem break_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.break code)) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeBp) :=
  _root_.break_spec_raw s w code hfetch hdecode hexec

theorem syscall_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.syscall code)) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeSys) :=
  _root_.syscall_spec_raw s w code hfetch hdecode hexec

/-! ## Coprocessor 0 -/

theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 4, 2 => read s.cp0UserLocal
      | 7, 0 => read s.cp0HWREna
      | 8, 0 => read s.cp0BadVAddr
      | 8, 1 => read s.cp0BadInstr
      | 8, 2 => read s.cp0BadInstrP
      | 9, 0 => read s.cp0Count
      | 11, 0 => read s.cp0Compare
      | 12, 0 => read (statusValue s)
      | 12, 1 => read 0xE0000000#32
      | 12, 2 => read 0#32
      | 13, 0 => read (s.cp0Cause ||| (s.hwInt.setWidth 32 <<< 10) |||
          (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32))
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read (0x80000980#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) |||
          (s.cp0ConfigKU.setWidth 32 <<< 25) ||| s.cp0ConfigK0.setWidth 32)
      | 16, 1 => read 0x80000001#32
      | 16, 2 => read 0x80000000#32
      | 16, 3 => read 0x8C003000#32
      | 16, 4 => read 0x80FC0000#32
      | 16, 5 => read (0x00002010#32 ||| (if s.cp0Config5SBRI then 0x40#32 else 0#32))
      | 17, 0 => read (if s.llBit then 1#32 else 0#32)
      | 30, 0 => read s.cp0ErrorEpc
      | 31, 2 => read (s.cp0KScratch 0)
      | 31, 3 => read (s.cp0KScratch 1)
      | 31, 4 => read (s.cp0KScratch 2)
      | 31, 5 => read (s.cp0KScratch 3)
      | 31, 6 => read (s.cp0KScratch 4)
      | 31, 7 => read (s.cp0KScratch 5)
      | _, _ => read 0#32) :=
  _root_.mfc0_spec_raw s w rt rd sel hfetch hdecode hpb hcp0 hexec

theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match rd.toNat, sel.toNat with
      | 4, 2 => { s with cp0UserLocal := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 7, 0 =>
        { s with cp0HWREna := readReg s (regIdxSpec rt) &&& hwrenaWriteMask, pc := s.pc + 4#32 }
      | 9, 0 => { s with cp0Count := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 11, 0 =>
        { s with cp0Compare := readReg s (regIdxSpec rt), cp0TimerInt := false, pc := s.pc + 4#32 }
      | 12, 0 =>
        { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 1 =>
        { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 =>
        { s with
              cp0ConfigK0 := ccaWrite s.cp0ConfigK0 ((readReg s (regIdxSpec rt)).setWidth 3)
              cp0ConfigK23 := ccaWrite s.cp0ConfigK23 ((readReg s (regIdxSpec rt) >>> 28).setWidth 3)
              cp0ConfigKU := ccaWrite s.cp0ConfigKU ((readReg s (regIdxSpec rt) >>> 25).setWidth 3)
              pc := s.pc + 4#32 }
      | 16, 5 =>
        { s with cp0Config5SBRI := readReg s (regIdxSpec rt) &&& 0x40#32 != 0#32, pc := s.pc + 4#32 }
      | 17, 0 =>
        { s with llBit := s.llBit && readReg s (regIdxSpec rt) &&& 1#32 != 0#32, pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 31, 2 => { s with cp0KScratch := fun j => if j = 0 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 3 => { s with cp0KScratch := fun j => if j = 1 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 4 => { s with cp0KScratch := fun j => if j = 2 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 5 => { s with cp0KScratch := fun j => if j = 3 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 6 => { s with cp0KScratch := fun j => if j = 4 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | 31, 7 => { s with cp0KScratch := fun j => if j = 5 then readReg s (regIdxSpec rt)
                    else s.cp0KScratch j, pc := s.pc + 4#32 }
      | _, _ => { s with pc := s.pc + 4#32 }) :=
  _root_.mtc0_spec_raw s w rt rd sel hfetch hdecode hpb hcp0 hexec

theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }) :=
  _root_.eret_spec_raw s w hfetch hdecode hpb hcp0 hexec


/-! ## Operating modes and reset -/

theorem cp0_instruction_user_mode_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop0 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cp0Usable s = false) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeCpU 0#32) :=
  _root_.cp0_instruction_user_mode_unusable s w instr hfetch hdecode huses hnb hcu hexec

theorem cp0Usable_false_iff (s : State) :
    cp0Usable s = false ↔ userMode s = true :=
  _root_.cp0Usable_false_iff s

theorem userMode_iff (s : State) :
    userMode s = true ↔
      (s.cp0Status &&& statusUmMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
        s.cp0Status &&& statusErlMask = 0#32) :=
  _root_.userMode_iff s

theorem exception_from_user_mode_enters_kernel_mode (s : State) (code ce : W32)
    (hu : userMode s = true) :
    kernelMode (exceptionEntry s code ce) = true ∧ userMode (exceptionEntry s code ce) = false ∧
      (exceptionEntry s code ce).cp0Status &&& statusUmMask ≠ 0#32 ∧
      (exceptionEntry s code ce).cp0Status &&& statusExlMask = statusExlMask :=
  _root_.exception_from_user_mode_enters_kernel_mode s code ce hu

theorem exceptionEntry_enters_kernel_mode (s : State) (code ce : W32) :
    kernelMode (exceptionEntry s code ce) = true :=
  _root_.exceptionEntry_enters_kernel_mode s code ce

theorem eret_to_user_mode (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none)
    (herl : s.cp0Status &&& statusErlMask = 0#32) (hexl : s.cp0Status &&& statusExlMask ≠ 0#32)
    (hum : s.cp0Status &&& statusUmMask ≠ 0#32) (hexec : executesInstr s = true) :
    (step s).pc = s.cp0Epc ∧ userMode (step s) = true :=
  _root_.eret_to_user_mode s w hfetch hdecode hpb herl hexl hum hexec

theorem resetException_spec (s : State) :
    (resetException s).pc = 0xBFC00000#32 ∧
    (resetException s).cp0Status &&& statusBevMask = statusBevMask ∧
    (resetException s).cp0Status &&& statusErlMask = statusErlMask ∧
    (resetException s).cp0Cause &&& causeDcMask = 0#32 ∧
    ebaseValue (resetException s) = 0x80000000#32 ∧
    configValue (resetException s) = 0xA4000982#32 ∧
    (resetException s).cp0ErrorEpc = (if s.pendingBranch.isSome then s.pc - 4#32 else s.pc) ∧
    (resetException s).pendingBranch = none ∧
    kernelMode (resetException s) = true ∧
    exceptionVector (resetException s) = 0xBFC00380#32 :=
  _root_.resetException_spec s

theorem resetState_spec :
    resetState.pc = 0xBFC00000#32 ∧ resetState.cp0Status = 0x00400004#32 ∧
    resetState.cp0Cause = 0#32 ∧ resetState.cp0Epc = 0#32 ∧ resetState.cp0BadVAddr = 0#32 ∧
    resetState.cp0ErrorEpc = 0#32 ∧ ebaseValue resetState = 0x80000000#32 ∧
    configValue resetState = 0xA4000982#32 ∧ kernelMode resetState = true ∧
    exceptionVector resetState = 0xBFC00380#32 ∧ resetState.pendingBranch = none ∧
    resetState.llBit = false ∧ resetState.regs = Array.replicate 32 0#32 ∧
    resetState.fpRegs = Array.replicate 32 0#64 ∧ resetState.fcsr = 0#32 ∧
    resetState.cp0Count = 0#32 ∧ resetState.cp0Compare = 0#32 ∧ resetState.cp0TimerInt = false ∧
    resetState.cp0HWREna = 0#32 :=
  _root_.resetState_spec

theorem hostedStart_is_reset_then_boot :
    hostedStart = bootConvention textBase resetState ∧ hostedStart = initialState textBase :=
  _root_.hostedStart_is_reset_then_boot

/-! ## Timer and hardware registers -/

theorem step_count_advances (s : State) (hdc : countEnabled s = true)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count + 1#32 :=
  _root_.step_count_advances s hdc hw

theorem step_count_stopped (s : State) (hdc : countEnabled s = false)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count :=
  _root_.step_count_stopped s hdc hw

theorem step_timer_match_sets_ti (s : State) (h : (step s).cp0Count = (step s).cp0Compare) :
    (step s).cp0TimerInt = true :=
  _root_.step_timer_match_sets_ti s h

theorem step_timerInt (s : State) (hw : fetchesTimerWrite s = false) :
    (step s).cp0TimerInt = (s.cp0TimerInt || (step s).cp0Count == s.cp0Compare) ∧
      (step s).cp0Compare = s.cp0Compare :=
  _root_.step_timerInt s hw

theorem mtc0_count_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 9#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Count =
      if countEnabled s then readReg s (regIdxSpec rt) + 1#32 else readReg s (regIdxSpec rt) :=
  _root_.mtc0_count_spec s w rt hfetch hdecode hpb hcp0 hexec

theorem mtc0_compare_clears_ti (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 11#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Compare = readReg s (regIdxSpec rt) ∧
      (step s).cp0TimerInt = ((step s).cp0Count == readReg s (regIdxSpec rt)) ∧
      (step s).cp0Count = (if countEnabled s then s.cp0Count + 1#32 else s.cp0Count) :=
  _root_.mtc0_compare_clears_ti s w rt hfetch hdecode hpb hcp0 hexec

theorem causeValue_timer (s : State) (h : s.cp0TimerInt = true) :
    causeValue s = s.cp0Cause ||| hwIntBits s ||| causeTiMask ||| causeIp7Mask :=
  _root_.causeValue_timer s h

theorem rdhwr_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd sel))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if sel != 0#32 then takeException s excCodeRI else
      match hwrValue s rd with
      | some v =>
        if rdhwrAllowed s rd then
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
        else takeException s excCodeRI
      | none => takeException s excCodeRI) :=
  _root_.rdhwr_spec_raw s w rt rd sel hfetch hdecode hpb hexec

theorem hwrValue_cpuNum (s : State) : hwrValue s 0#32 = some 0#32 :=
  _root_.hwrValue_cpuNum s

theorem hwrValue_synciStep (s : State) : hwrValue s 1#32 = some 0#32 :=
  _root_.hwrValue_synciStep s

theorem hwrValue_cc (s : State) : hwrValue s 2#32 = some s.cp0Count :=
  _root_.hwrValue_cc s

theorem hwrValue_ccRes (s : State) : hwrValue s 3#32 = some 1#32 :=
  _root_.hwrValue_ccRes s

theorem hwrValue_unimplemented (s : State) (rd : W32) (h : 4 ≤ rd.toNat) (h5 : rd.toNat ≠ 5)
    (h29 : rd.toNat ≠ 29) : hwrValue s rd = none :=
  _root_.hwrValue_unimplemented s rd h h5 h29

theorem rdhwr_reserved_unimplemented (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd sel))
    (hpb : s.pendingBranch = none) (hrd : 4 ≤ rd.toNat) (h5 : rd.toNat ≠ 5) (h29 : rd.toNat ≠ 29)
    (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.rdhwr_reserved_unimplemented s w rt rd sel hfetch hdecode hpb hrd h5 h29 hexec

theorem rdhwr_reserved_sel (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd sel))
    (hpb : s.pendingBranch = none) (hsel : sel ≠ 0#32) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.rdhwr_reserved_sel s w rt rd sel hfetch hdecode hpb hsel hexec

theorem rdhwr_reserved_not_enabled (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = false)
    (hen : (s.cp0HWREna >>> rd) &&& 1#32 = 0#32) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.rdhwr_reserved_not_enabled s w rt rd sel hfetch hdecode hpb hcp0 hen hexec

theorem rdhwr_allowed (s : State) (w rt rd v : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd 0#32))
    (hpb : s.pendingBranch = none) (hv : hwrValue s rd = some v)
    (hacc : cp0Usable s = true ∨ (s.cp0HWREna >>> rd) &&& 1#32 ≠ 0#32) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } :=
  _root_.rdhwr_allowed s w rt rd v hfetch hdecode hpb hv hacc hexec

theorem hwrena_write_masked (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 7#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0HWREna = readReg s (regIdxSpec rt) &&& 0x2000002F#32 :=
  _root_.hwrena_write_masked s w rt hfetch hdecode hpb hcp0 hexec

theorem resetException_timer (s : State) :
    (resetException s).cp0HWREna = 0#32 ∧ (resetException s).cp0Count = s.cp0Count ∧
      (resetException s).cp0Compare = s.cp0Compare ∧
      (resetException s).cp0TimerInt = s.cp0TimerInt :=
  _root_.resetException_timer s

/-! ## Floating point -/

theorem fp_coprocessor_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop1 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cu1Enabled s = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeCoprocessorUnusable s) :=
  _root_.fp_coprocessor_unusable s w instr hfetch hdecode huses hnb hcu hexec

theorem fpCompletesS_trap (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = true)
    (h : fpCompletesS s fd r = s') :
    causeExcCode s' = 15#32 ∧ s'.fpRegs = s.fpRegs ∧ s'.fcsr = fcsrTrapped s.fcsr r.2 ∧
      s'.regs = s.regs ∧ s'.physMem = s.physMem ∧ s'.pc = exceptionVector s :=
  _root_.fpCompletesS_trap s s' fd r hen h

theorem fpCompletesS_ok (s s' : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hen : Mips.Fp.fpeEnabled s.fcsr r.2 = false) (hsize : s.fpRegs.size = 32)
    (h : fpCompletesS s fd r = s') :
    readFpReg s' (regIdx fd) = r.1 ∧ s'.fcsr = Mips.Fp.raiseFlags s.fcsr r.2 ∧
      s'.pc = s.pc + 4#32 ∧ s'.regs = s.regs :=
  _root_.fpCompletesS_ok s s' fd r hen hsize h

theorem addS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) :=
  _root_.addS_spec_raw s w fd fs ft hfetch hdecode hpb hcu hexec

theorem addD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) :=
  _root_.addD_spec_raw s w fd fs ft hfetch hdecode hpb hcu hexec

theorem cvtWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) :=
  _root_.cvtWS_spec_raw s w fd fs hfetch hdecode hpb hcu hexec

theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 }) :=
  _root_.mfc1_spec_raw s w rt fs hfetch hdecode hpb hcu hexec

theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 }) :=
  _root_.lwc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu hexec

theorem lwc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm)) :=
  _root_.lwc1_misaligned_spec s w rs ft imm hfetch hdecode hpb hcu hmisaligned hexec

theorem cfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match Mips.Fp.readControl s.fcsr fs.toNat with
      | some v => { (writeReg s (regIdx rt) v) with pc := (writeReg s (regIdx rt) v).pc + 4#32 }
      | none => takeException s excCodeRI) :=
  _root_.cfc1_spec_raw s w rt fs hfetch hdecode hpb hcu hexec

theorem ctc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none => takeException s excCodeRI
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else { s with fcsr := f, pc := s.pc + 4#32 }) :=
  _root_.ctc1_spec_raw s w rt fs hfetch hdecode hpb hcu hexec

theorem fcsr_ctc1_cfc1_roundtrip (fcsr v : W32) :
    ∃ f, Mips.Fp.writeControl fcsr 31 v = some f ∧ f = v &&& Mips.Fp.fcsrWritableMask ∧
      Mips.Fp.readControl f 31 = some ((v &&& Mips.Fp.fcsrWritableMask) ||| Mips.Fp.fcsr2008Bits) :=
  _root_.fcsr_ctc1_cfc1_roundtrip fcsr v

/-! ## Address translation: the Fixed Mapping MMU, and the loader -/

theorem fixedMappingPA_kuseg_erl0 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA false va = va + 0x40000000#32 ∧
      (fixedMappingPA false va).toNat = va.toNat + 0x40000000 :=
  _root_.fixedMappingPA_kuseg_erl0 va h

theorem fixedMappingPA_kuseg_erl1 (va : W32) (h : va.toNat < 0x80000000) :
    fixedMappingPA true va = va :=
  _root_.fixedMappingPA_kuseg_erl1 va h

theorem fixedMappingPA_kseg0 (erl : Bool) (va : W32) (h1 : 0x80000000 ≤ va.toNat)
    (h2 : va.toNat < 0xA0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0x80000000 :=
  _root_.fixedMappingPA_kseg0 erl va h1 h2

theorem fixedMappingPA_kseg1 (erl : Bool) (va : W32) (h1 : 0xA0000000 ≤ va.toNat)
    (h2 : va.toNat < 0xC0000000) : (fixedMappingPA erl va).toNat = va.toNat - 0xA0000000 :=
  _root_.fixedMappingPA_kseg1 erl va h1 h2

theorem fixedMappingPA_kseg23 (erl : Bool) (va : W32) (h : 0xC0000000 ≤ va.toNat) :
    fixedMappingPA erl va = va :=
  _root_.fixedMappingPA_kseg23 erl va h

theorem fixedMappingPA_kseg0_kseg1_alias (erl : Bool) (x : W32) (hx : x.toNat < 0x20000000) :
    fixedMappingPA erl (0x80000000#32 + x) = x ∧ fixedMappingPA erl (0xA0000000#32 + x) = x :=
  _root_.fixedMappingPA_kseg0_kseg1_alias erl x hx

theorem translate_user_kernel_address (s : State) (va : W32) (hum : userMode s = true)
    (hk : isUseg va = false) : translate s va = none :=
  _root_.translate_user_kernel_address s va hum hk

theorem translate_erl1_kuseg_identity (s : State) (va : W32) (herl : erlSet s = true)
    (h : va.toNat < 0x80000000) : translate s va = some va :=
  _root_.translate_erl1_kuseg_identity s va herl h

theorem step_fetch_user_kernel_address (s : State) (hum : userMode s = true)
    (hk : isUseg s.pc = false) (hexec : executesInstr s = true) : step s = timerTick (takeAddressException s excCodeAdEL s.pc) :=
  _root_.step_fetch_user_kernel_address s hum hk hexec

theorem lw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm :=
  _root_.lw_user_kernel_address s w rs rt imm hfetch hdecode hpb hum hk hexec

theorem sw_user_kernel_address (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) (hum : userMode s = true)
    (hk : isUseg (readReg s (regIdxSpec rs) + signExt16 imm) = false) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdES (readReg s (regIdxSpec rs) + signExt16 imm)) ∧
      (step s).physMem = s.physMem ∧
      (step s).cp0BadVAddr = readReg s (regIdxSpec rs) + signExt16 imm :=
  _root_.sw_user_kernel_address s w rs rt imm hfetch hdecode hpb hum hk hexec

theorem kseg1_store_visible_through_kseg0 (s s' : State) (x v : W32) (hk : kernelMode s = true)
    (hx : x.toNat < 0x20000000) (hal : x.toNat % 4 = 0)
    (h : writeMemWord s (0xA0000000#32 + x) v = some s') :
    readMemWord s' (0x80000000#32 + x) = some v :=
  _root_.kseg1_store_visible_through_kseg0 s s' x v hk hx hal h

theorem load_readMemWord (p : Program) (a w : W32) (hw : p.get? a = some w)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (load p) a = some w :=
  _root_.load_readMemWord p a w hw halign hdisj

theorem load_step_fetches_image (p : Program) (w : W32) (instr : Instruction)
    (hw : p.get? textBase = some w) (hdecode : decode w = some instr)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ textBase → loadAddr b ≠ loadAddr textBase) :
    step (load p) = timerTick (execInstr (load p) instr) :=
  _root_.load_step_fetches_image p w instr hw hdecode halign hdisj

theorem loadAtReset_readMemWord_kseg (p : Program) (a w : W32) (hw : p.get? a = some w)
    (hk : 0x80000000 ≤ a.toNat)
    (halign : ∀ b v, p.get? b = some v → b.toNat % 4 = 0)
    (hdisj : ∀ b v, p.get? b = some v → b ≠ a → loadAddr b ≠ loadAddr a) :
    readMemWord (loadAtReset p) a = some w :=
  _root_.loadAtReset_readMemWord_kseg p a w hw hk halign hdisj

theorem canonicalVAddr_loadAddr (va : VAddr) (h : isKseg1 va = false) :
    canonicalVAddr (loadAddr va) = va :=
  _root_.canonicalVAddr_loadAddr va h

theorem canonicalVAddr_loadAddr_kseg1 (va : VAddr) (h : isKseg1 va = true) :
    canonicalVAddr (loadAddr va) = va - 0x20000000#32 :=
  _root_.canonicalVAddr_loadAddr_kseg1 va h

theorem loadAddr_canonicalVAddr (pa : PAddr)
    (h : ¬ (0x20000000 ≤ pa.toNat ∧ pa.toNat < 0x40000000)) :
    loadAddr (canonicalVAddr pa) = pa :=
  _root_.loadAddr_canonicalVAddr pa h

/-! ## Self-modifying code and the hosted environment -/

theorem sw_next_instruction_is_fetched (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true) (hexec : executesInstr s = true) :
    (step s).pc = s.pc + 4#32 ∧
      readMemWord (step s) (step s).pc = some (readReg s (regIdxSpec rt)) :=
  _root_.sw_next_instruction_is_fetched s w rs rt imm hfetch hdecode hpb haddr hacc hexec

theorem store_changes_next_instruction (s : State) (w rs rt imm : W32) (instr' : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true)
    (hnew : decode (readReg s (regIdxSpec rt)) = some instr') (hexec : executesInstr s = true)
    (hexec2 : executesInstr (step s) = true) :
    step (step s) = timerTick (execInstr (step s) instr') :=
  _root_.store_changes_next_instruction s w rs rt imm instr' hfetch hdecode hpb haddr hacc hnew hexec hexec2

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
    (hpb : h.machine.pendingBranch = none) (hexec : executesInstr h.machine = true) :
    hostStep env h =
      .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
              out := h.out ++ toString (asSigned (readReg h.machine (regIdxSpec 4#32))) } :=
  _root_.hosted_print_int env h w code hstop hon hfetch hdecode hv0 hpb hexec

theorem hosted_exit (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 10#32) (hexec : executesInstr h.machine = true) :
    hostStep env h = .halt .exit :=
  _root_.hosted_exit env h w code hstop hon hfetch hdecode hv0 hexec

theorem runHosted_preserves_zero_register (env : HostEnv) (n : Nat) (h : Hosted) :
    readReg (runHosted env n h).final.machine 0 = readReg h.machine 0 :=
  _root_.runHosted_preserves_zero_register env n h

/-! ## Interrupts, standby, IntCtl and SRSCtl -/

theorem step_interrupt (s : State) (h : interruptTaken s = true) :
    step s = timerTick (takeInterrupt s) :=
  _root_.step_interrupt s h

theorem interruptTaken_iff (s : State) :
    interruptTaken s = true ↔
      s.cp0Status &&& statusIeMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
      s.cp0Status &&& statusErlMask = 0#32 ∧
      causeValue s &&& s.cp0Status &&& statusImMask ≠ 0#32 :=
  _root_.interruptTaken_iff s

theorem no_interrupt_ie0 (s : State) (h : s.cp0Status &&& statusIeMask = 0#32) :
    interruptTaken s = false :=
  _root_.no_interrupt_ie0 s h

theorem no_interrupt_exl (s : State) (h : s.cp0Status &&& statusExlMask ≠ 0#32) :
    interruptTaken s = false :=
  _root_.no_interrupt_exl s h

theorem no_interrupt_erl (s : State) (h : s.cp0Status &&& statusErlMask ≠ 0#32) :
    interruptTaken s = false :=
  _root_.no_interrupt_erl s h

theorem no_interrupt_masked (s : State) (h : interruptRequests s = 0#32) :
    interruptTaken s = false :=
  _root_.no_interrupt_masked s h

theorem takeInterrupt_not_in_delay_slot (s : State) (hexl : s.cp0Status &&& statusExlMask = 0#32)
    (hpb : s.pendingBranch = none) :
    (takeInterrupt s).cp0Epc = s.pc ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).cp0Status = s.cp0Status ||| statusExlMask ∧
      (takeInterrupt s).pc = interruptVector s ∧
      (takeInterrupt s).standby = false :=
  _root_.takeInterrupt_not_in_delay_slot s hexl hpb

theorem takeInterrupt_in_delay_slot (s : State) (t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (takeInterrupt s).cp0Epc = s.pc - 4#32 ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).pendingBranch = none ∧
      (takeInterrupt s).pc = interruptVector s :=
  _root_.takeInterrupt_in_delay_slot s t hexl hpb

theorem interruptVector_iv0 (s : State) (h : s.cp0Cause &&& causeIvMask = 0#32) :
    interruptVector s = exceptionVector s :=
  _root_.interruptVector_iv0 s h

theorem interruptVector_iv1_bev0 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask = 0#32) :
    interruptVector s = ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x200#32 :=
  _root_.interruptVector_iv1_bev0 s h hbev

theorem interruptVector_iv1_bev1 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask ≠ 0#32) :
    interruptVector s = 0xBFC00400#32 :=
  _root_.interruptVector_iv1_bev1 s h hbev

theorem mtc0_cause_requests_software_interrupt (s : State) (w rt : W32) (i : Nat)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 13#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hi : i = 8 ∨ i = 9) (hip : (readReg s (regIdxSpec rt)).getLsbD i = true)
    (him : s.cp0Status.getLsbD i = true) (hen : interruptsEnabled s = true) :
    interruptRequests (step s) ≠ 0#32 ∧ interruptTaken (step s) = true :=
  _root_.mtc0_cause_requests_software_interrupt s w rt i hfetch hdecode hpb hcp0 hexec hi hip him hen

theorem timer_requests_interrupt (s : State) (hti : s.cp0TimerInt = true)
    (him : s.cp0Status.getLsbD 15 = true) :
    interruptRequests s ≠ 0#32 :=
  _root_.timer_requests_interrupt s hti him

theorem step_hwInt (s : State) : (step s).hwInt = s.hwInt :=
  _root_.step_hwInt s

theorem wait_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick ({ s with standby := interruptRequests s == 0#32, pc := s.pc + 4#32 }) :=
  _root_.wait_spec_raw s w code hfetch hdecode hpb hcp0 hexec

theorem step_standby_stays (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s = 0#32) :
    step s = timerTick s :=
  _root_.step_standby_stays s hsb hreq

theorem step_standby_restarts (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s ≠ 0#32) (hen : interruptsEnabled s = false) :
    step s = timerTick { s with standby := false } :=
  _root_.step_standby_restarts s hsb hreq hen

theorem step_standby_interrupt (s : State) (_hsb : s.standby = true) (h : interruptTaken s = true)
    (hpb : s.pendingBranch = none) :
    step s = timerTick (takeInterrupt s) ∧ (step s).cp0Epc = s.pc ∧ (step s).standby = false :=
  _root_.step_standby_interrupt s _hsb h hpb

theorem intCtlValue_fields :
    intCtlValue >>> 29 = 7#32 ∧ (intCtlValue >>> 26) &&& 7#32 = 0#32 ∧
      (intCtlValue >>> 23) &&& 7#32 = 0#32 ∧ (intCtlValue >>> 5) &&& 31#32 = 0#32 :=
  _root_.intCtlValue_fields

theorem srsCtlValue_fields :
    (srsCtlValue >>> 26) &&& 15#32 = 0#32 ∧ (srsCtlValue >>> 12) &&& 15#32 = 0#32 ∧
      (srsCtlValue >>> 6) &&& 15#32 = 0#32 ∧ srsCtlValue &&& 15#32 = 0#32 :=
  _root_.srsCtlValue_fields

theorem mfc0_srsctl_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt 12#32 2#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0#32) with pc := (writeReg s (regIdxSpec rt) 0#32).pc + 4#32 } :=
  _root_.mfc0_srsctl_spec s w rt hfetch hdecode hpb hcp0 hexec

theorem rdpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) :=
  _root_.rdpgpr_spec_raw s w rd rt hfetch hdecode hpb hcp0 hexec

theorem wrpgpr_spec_raw (s : State) (w rd rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wrpgpr rd rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt))).pc + 4#32 }) :=
  _root_.wrpgpr_spec_raw s w rd rt hfetch hdecode hpb hcp0 hexec

/-! ## The refinement of the manual specification -/

theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle Manual.decodeDiagram (Refine.abs s) =
      some (Refine.abs (step s)) :=
  _root_.Refine.step_eq_manual s hs

theorem step_refines_manual (s : State) (hs : Refine.Inv s) :
    Manual.Step Manual.modelImpl Manual.decodeDiagram (Refine.abs s) (Refine.abs (step s)) :=
  _root_.Refine.step_refines_manual s hs

theorem run_refines_manual (s : State) (hs : Refine.Inv s) (n : Nat) :
    Manual.InstructionTimes Manual.modelImpl Manual.modelOracle Manual.decodeDiagram n (Refine.abs s) =
      some (Refine.abs (run s n)) :=
  _root_.Refine.run_refines_manual s hs n

theorem step_unique_of_choiceFree (s : State) (hs : Refine.Inv s)
    (h : Manual.ChoiceFree Manual.modelImpl Manual.decodeDiagram (Refine.abs s) = true) (a' : Manual.Arch)
    (h' : Manual.Step Manual.modelImpl Manual.decodeDiagram (Refine.abs s) a') : a' = Refine.abs (step s) :=
  _root_.Refine.step_unique_of_choiceFree s hs h a' h'

theorem modelOracle_valid : Manual.modelOracle.Valid :=
  _root_.Refine.modelOracle_valid

theorem manual_step_deterministic (i : Manual.Impl) (dec : W32 → Option Instruction)
    (a a₁ a₂ : Manual.Arch) (h : Manual.ChoiceFree i dec a = true) (h₁ : Manual.Step i dec a a₁)
    (h₂ : Manual.Step i dec a a₂) : a₁ = a₂ :=
  _root_.Refine.manual_step_deterministic i dec a a₁ a₂ h h₁ h₂

theorem interrupt_choice_exists (i : Manual.Impl) (dec : W32 → Option Instruction) (a : Manual.Arch)
    (h : Manual.InterruptTaken i a = true) :
    ∃ o₁ o₂ : Manual.Oracle, o₁.Valid ∧ o₂.Valid ∧
      Manual.InstructionTime i o₁ dec a ≠ Manual.InstructionTime i o₂ dec a :=
  _root_.Refine.interrupt_choice_exists i dec a h

theorem choiceFree_exact (dec : W32 → Option Instruction) (a : Manual.Arch)
    (h : Manual.ChoiceFree Manual.modelImpl dec a = false) :
    ∃ o₁ o₂ : Manual.Oracle, o₁.Valid ∧ o₂.Valid ∧
      Manual.InstructionTime Manual.modelImpl o₁ dec a ≠ Manual.InstructionTime Manual.modelImpl o₂ dec a :=
  _root_.Refine.choiceFree_exact dec a h

theorem modelImpl_valid : Manual.modelImpl.Valid :=
  _root_.Manual.modelImpl_valid

theorem decoderSound_decode : Manual.DecoderSound decode :=
  _root_.Refine.decoderSound_decode

theorem decode_diagram_sound (w : W32) (i : Instruction) (h : Manual.Decode w = .instr i) :
    Manual.enc i = some w :=
  _root_.Refine.decode_diagram_sound w i h

theorem decode_diagram_complete (i : Instruction) (w : W32) (h : Manual.enc i = some w) :
    ∃ j, Manual.Decode w = .instr j ∧ Manual.enc j = some w :=
  _root_.Refine.decode_diagram_complete i w h

theorem decode_agrees_manual (w : W32) (i : Instruction) (h : decode w = some i) :
    Manual.Decode w = .instr i :=
  _root_.Refine.decode_agrees w i h

theorem decode_none_manual (w : W32) (h : decode w = none) (i : Instruction)
    (hi : Manual.Decode w = .instr i) (a : Manual.Arch) : Manual.ConsultsOracle i a = true :=
  _root_.Refine.rejected_consults i (_root_.Refine.decode_none_rejected w h i hi) a

theorem decoderSound_decodeDiagram : Manual.DecoderSound Manual.decodeDiagram :=
  _root_.Refine.decoderSound_decodeDiagram

theorem resetException_refines_manual (s : State) (h : Refine.StatusImplemented s) :
    Refine.abs (resetException s) = Manual.ResetException Manual.modelOracle (Refine.abs s) :=
  _root_.Refine.resetException_refines_manual s h

theorem resetState_refines_manual :
    Refine.abs resetState = Manual.ResetException Manual.modelOracle (Refine.abs powerOnState) :=
  _root_.Refine.resetState_refines_manual

theorem step_preserves_inv (s : State) (h : Refine.Inv s) : Refine.Inv (step s) :=
  _root_.Refine.step_preserves_inv s h

theorem inv_resetState : Refine.Inv resetState :=
  _root_.Refine.inv_resetState

theorem inv_hostedStart : Refine.Inv hostedStart :=
  _root_.Refine.inv_hostedStart

theorem inv_load (p : Program) : Refine.Inv (load p) :=
  _root_.Refine.inv_load p

/-! ## The IEEE rounding core is proved correct

`Mips.Fp.Format.RoundSpec` (`Semantics/FpOpsSpec.lean`) is the IEEE 754 definition the manual
references, written from the manual and not from the core: the values of the encodings
(`Format.value`, Table 6.2), correct rounding to the representable values in each direction
(`CorrectlyRounded`, Table 6.10, ties to even), overflow and its result (§6.7.2.5, Table 6.14),
inexact (§6.7.2.6), tininess after rounding (§6.7.2.3). The exact result is a `Cut` (its order
relation with the rationals) so that `√x` can be stated. -/

theorem value_eq_toExact (f : Mips.Fp.Format) (n : Nat) (hn : n < 2 ^ f.width)
    (he : f.expField n ≠ f.expMax) : f.value n = some (f.toExact n).toRat :=
  _root_.Mips.Fp.value_eq_toExact f n hn he

theorem roundCore_correct_binary32 (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact) (hw : w.sig ≠ 0) :
    Mips.Fp.binary32.RoundSpec rm (Mips.Fp.Cut.ofRat w.toRat) (Mips.Fp.binary32.roundCore rm false w) :=
  _root_.Mips.Fp.roundCore_correct_binary32 rm w hw

theorem roundCore_correct_binary64 (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact) (hw : w.sig ≠ 0) :
    Mips.Fp.binary64.RoundSpec rm (Mips.Fp.Cut.ofRat w.toRat) (Mips.Fp.binary64.roundCore rm false w) :=
  _root_.Mips.Fp.roundCore_correct_binary64 rm w hw

theorem roundSpec_representable (f : Mips.Fp.Format) {rm : Mips.Fp.RoundingMode} {c : Mips.Fp.Cut}
    {R : Mips.Fp.Format.Rounded} (h : f.RoundSpec rm c R) (hov : R.overflow = false) :
    ∃ r, f.value R.bits = some r ∧ Mips.Fp.CorrectlyRounded f.Representable f.UnboundedEven rm c r :=
  _root_.Mips.Fp.roundSpec_representable f h hov

theorem roundCore_flush_tiny (f : Mips.Fp.Format) (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact)
    (hw : w.sig ≠ 0) (ht : w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = ⟨f.zero w.sign, false, true, true⟩ :=
  _root_.Mips.Fp.roundCore_flush_tiny f rm w hw ht

theorem roundCore_flush_normal (f : Mips.Fp.Format) (rm : Mips.Fp.RoundingMode) (w : Mips.Fp.Exact)
    (hw : w.sig ≠ 0) (ht : ¬ w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = f.roundCore rm false w :=
  _root_.Mips.Fp.roundCore_flush_normal f rm w hw ht

theorem f32Add_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x + y)) R ∧
      Mips.Fp.f32Add e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f32Add_correct e he ha hb hxy

theorem f32Sub_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x - y)) R ∧
      Mips.Fp.f32Sub e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f32Sub_correct e he ha hb hxy

theorem f32Mul_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x * y)) R ∧
      Mips.Fp.f32Mul e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f32Mul_correct e he ha hb hx hy

theorem f32Div_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 32} {x y : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hb : Mips.Fp.binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x / y)) R ∧
      Mips.Fp.f32Div e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f32Div_correct e he ha hb hx hy

theorem f32Sqrt_correct (e : Mips.Fp.Env) (he : e.flush = false) {a : BitVec 32} {x : Rat}
    (ha : Mips.Fp.binary32.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary32.RoundSpec e.rm (Mips.Fp.Cut.sqrt x) R ∧
      Mips.Fp.f32Sqrt e a = (BitVec.ofNat 32 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f32Sqrt_correct e he ha hx

theorem f64Add_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x + y)) R ∧
      Mips.Fp.f64Add e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f64Add_correct e he ha hb hxy

theorem f64Sub_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x - y)) R ∧
      Mips.Fp.f64Sub e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f64Sub_correct e he ha hb hxy

theorem f64Mul_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x * y)) R ∧
      Mips.Fp.f64Mul e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f64Mul_correct e he ha hb hx hy

theorem f64Div_correct (e : Mips.Fp.Env) (he : e.flush = false) {a b : BitVec 64} {x y : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hb : Mips.Fp.binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.ofRat (x / y)) R ∧
      Mips.Fp.f64Div e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f64Div_correct e he ha hb hx hy

theorem f64Sqrt_correct (e : Mips.Fp.Env) (he : e.flush = false) {a : BitVec 64} {x : Rat}
    (ha : Mips.Fp.binary64.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Mips.Fp.Format.Rounded, Mips.Fp.binary64.RoundSpec e.rm (Mips.Fp.Cut.sqrt x) R ∧
      Mips.Fp.f64Sqrt e a = (BitVec.ofNat 64 R.bits, R.flags e.enables) :=
  _root_.Mips.Fp.f64Sqrt_correct e he ha hx

/-! ## Every FP operand, the conversions, the compares, the FCSR

The reference definitions extend `Semantics/FpOpsSpec.lean` (definitions only, written from MD00082
Vol I-A Rev 6.01 ch.6 with `FIR.Has2008 = 0` and the MD00086 Vol II-A Rev 6.06 instruction pages):
the classes of an encoding (`Format.datum`, `IsSNaN`/`IsQNaN`, Table 6.2), the new QNaN (Table 6.3),
the NaN rule (`NaNResult`, §6.3.1.4-5), the signaled exceptions (`Signaled`, §6.7.2.3/5/6), rounding
under the whole FCSR including flush to zero (`RoundEnvSpec`, §6.7.2.4), each operation on every
operand (`AddSpec`, `MulSpec`, `DivSpec`, `SqrtSpec`, `SignOpSpec`, `ConvertSpec`, `WidenSpec`,
`FromIntSpec`, `ExactSpec`, `ToWordSpec`, `CompareSpec` with the 16-row `condTable`), the FCSR
update (`FcsrSpec`, §6.7.1, CheckFPException) and the multiply-add family as separate operations
(`MaddSpec`). -/

theorem newQNaN_binary32 : Mips.Fp.binary32.newQNaN = 0x7FC00000 :=
  _root_.Mips.Fp.newQNaN_binary32

theorem newQNaN_binary64 : Mips.Fp.binary64.newQNaN = 0x7FF8000000000000 :=
  _root_.Mips.Fp.newQNaN_binary64

theorem nanResult_first (f : Mips.Fp.Format) (ops : List Nat) (q : Nat)
    (hs : ops.find? (fun x => f.isSNaN x) = none)
    (h : ops.find? (fun x => f.isQNaN x) = some q) : f.nanResult ops = q :=
  _root_.Mips.Fp.Format.nanResult_first f ops q hs h

theorem nanResult_first_snan (f : Mips.Fp.Format) (ops : List Nat) (q : Nat)
    (h : ops.find? (fun x => f.isSNaN x) = some q) : f.nanResult ops = f.quiet q :=
  _root_.Mips.Fp.Format.nanResult_first_snan f ops q h

theorem f32Add_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary32.AddSpec e false (Mips.Fp.binary32.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary32.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f32Add e a b).1.toNat, (Mips.Fp.f32Add e a b).2) :=
  _root_.Mips.Fp.f32Add_spec e a b

theorem f32Sub_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary32.AddSpec e true (Mips.Fp.binary32.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary32.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f32Sub e a b).1.toNat, (Mips.Fp.f32Sub e a b).2) :=
  _root_.Mips.Fp.f32Sub_spec e a b

theorem f32Mul_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary32.MulSpec e (Mips.Fp.binary32.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary32.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f32Mul e a b).1.toNat, (Mips.Fp.f32Mul e a b).2) :=
  _root_.Mips.Fp.f32Mul_spec e a b

theorem f32Div_spec (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary32.DivSpec e (Mips.Fp.binary32.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary32.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f32Div e a b).1.toNat, (Mips.Fp.f32Div e a b).2) :=
  _root_.Mips.Fp.f32Div_spec e a b

theorem f32Sqrt_spec (e : Mips.Fp.Env) (a : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [a.toNat]
      (Mips.Fp.binary32.SqrtSpec e (Mips.Fp.binary32.FlushedIn e.flush a.toNat))
      ((Mips.Fp.f32Sqrt e a).1.toNat, (Mips.Fp.f32Sqrt e a).2) :=
  _root_.Mips.Fp.f32Sqrt_spec e a

theorem f64Add_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary64.AddSpec e false (Mips.Fp.binary64.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary64.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f64Add e a b).1.toNat, (Mips.Fp.f64Add e a b).2) :=
  _root_.Mips.Fp.f64Add_spec e a b

theorem f64Sub_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary64.AddSpec e true (Mips.Fp.binary64.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary64.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f64Sub e a b).1.toNat, (Mips.Fp.f64Sub e a b).2) :=
  _root_.Mips.Fp.f64Sub_spec e a b

theorem f64Mul_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary64.MulSpec e (Mips.Fp.binary64.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary64.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f64Mul e a b).1.toNat, (Mips.Fp.f64Mul e a b).2) :=
  _root_.Mips.Fp.f64Mul_spec e a b

theorem f64Div_spec (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (Mips.Fp.binary64.DivSpec e (Mips.Fp.binary64.FlushedIn e.flush a.toNat)
        (Mips.Fp.binary64.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f64Div e a b).1.toNat, (Mips.Fp.f64Div e a b).2) :=
  _root_.Mips.Fp.f64Div_spec e a b

theorem f64Sqrt_spec (e : Mips.Fp.Env) (a : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [a.toNat]
      (Mips.Fp.binary64.SqrtSpec e (Mips.Fp.binary64.FlushedIn e.flush a.toNat))
      ((Mips.Fp.f64Sqrt e a).1.toNat, (Mips.Fp.f64Sqrt e a).2) :=
  _root_.Mips.Fp.f64Sqrt_spec e a

theorem f64ToF32_spec (e : Mips.Fp.Env) (x : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [x.toNat]
      (Mips.Fp.Format.ConvertSpec Mips.Fp.binary64 Mips.Fp.binary32 e
        (Mips.Fp.binary64.FlushedIn e.flush x.toNat))
      ((Mips.Fp.f64ToF32 e x).1.toNat, (Mips.Fp.f64ToF32 e x).2) :=
  _root_.Mips.Fp.f64ToF32_spec e x

theorem f32ToF64_spec (fl : Bool) (x : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact fl [x.toNat]
      (Mips.Fp.Format.WidenSpec Mips.Fp.binary32 Mips.Fp.binary64 (Mips.Fp.binary32.FlushedIn fl x.toNat))
      ((Mips.Fp.f32ToF64 fl x).1.toNat, (Mips.Fp.f32ToF64 fl x).2) :=
  _root_.Mips.Fp.f32ToF64_spec fl x

theorem w32ToF32_spec (e : Mips.Fp.Env) (x : BitVec 32) :
    Mips.Fp.binary32.FromIntSpec e x.toInt ((Mips.Fp.w32ToF32 e x).1.toNat, (Mips.Fp.w32ToF32 e x).2) :=
  _root_.Mips.Fp.w32ToF32_spec e x

theorem w32ToF64_spec (x : BitVec 32) :
    Mips.Fp.binary64.ExactSpec (decide (x.toInt < 0)) x.toInt
      ((Mips.Fp.w32ToF64F x).1.toNat, (Mips.Fp.w32ToF64F x).2) :=
  _root_.Mips.Fp.w32ToF64_spec x

theorem f32ToW32_spec (rm : Mips.Fp.RoundingMode) (fl : Bool) (x : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact fl [x.toNat]
      (Mips.Fp.binary32.ToWordSpec rm (Mips.Fp.binary32.FlushedIn fl x.toNat))
      (Mips.Fp.f32ToW32 rm fl x) :=
  _root_.Mips.Fp.f32ToW32_spec rm fl x

theorem f64ToW32_spec (rm : Mips.Fp.RoundingMode) (fl : Bool) (x : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact fl [x.toNat]
      (Mips.Fp.binary64.ToWordSpec rm (Mips.Fp.binary64.FlushedIn fl x.toNat))
      (Mips.Fp.f64ToW32 rm fl x) :=
  _root_.Mips.Fp.f64ToW32_spec rm fl x

theorem f32ToW64_spec (rm : Mips.Fp.RoundingMode) (fl : Bool) (x : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact fl [x.toNat]
      (Mips.Fp.binary32.ToLongSpec rm (Mips.Fp.binary32.FlushedIn fl x.toNat))
      (Mips.Fp.f32ToW64 rm fl x) :=
  _root_.Mips.Fp.f32ToW64_spec rm fl x

theorem f64ToW64_spec (rm : Mips.Fp.RoundingMode) (fl : Bool) (x : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact fl [x.toNat]
      (Mips.Fp.binary64.ToLongSpec rm (Mips.Fp.binary64.FlushedIn fl x.toNat))
      (Mips.Fp.f64ToW64 rm fl x) :=
  _root_.Mips.Fp.f64ToW64_spec rm fl x

theorem w64ToF32_spec (e : Mips.Fp.Env) (x : BitVec 64) :
    Mips.Fp.binary32.FromIntSpec e x.toInt ((Mips.Fp.w64ToF32 e x).1.toNat, (Mips.Fp.w64ToF32 e x).2) :=
  _root_.Mips.Fp.w64ToF32_spec e x

theorem w64ToF64_spec (e : Mips.Fp.Env) (x : BitVec 64) :
    Mips.Fp.binary64.FromIntSpec e x.toInt ((Mips.Fp.w64ToF64 e x).1.toNat, (Mips.Fp.w64ToF64 e x).2) :=
  _root_.Mips.Fp.w64ToF64_spec e x

theorem condTable_formula : ∀ (cond : BitVec 4) (r : Mips.Fp.Format.Relation),
    Mips.Fp.fpCompare cond (decide (r = .un)) (decide (r = .lt)) (decide (r = .eq)) =
      Mips.Fp.condHolds cond.toNat r ∧
    (Mips.Fp.condTable cond.toNat).2.2.2.2 = cond.getLsbD 3 :=
  _root_.Mips.Fp.condTable_formula

theorem f32Compare_spec (cond : BitVec 4) (a b : BitVec 32) :
    Mips.Fp.binary32.CompareSpec cond a.toNat b.toNat (Mips.Fp.f32Compare cond a b) :=
  _root_.Mips.Fp.f32Compare_spec cond a b

theorem f64Compare_spec (cond : BitVec 4) (a b : BitVec 64) :
    Mips.Fp.binary64.CompareSpec cond a.toNat b.toNat (Mips.Fp.f64Compare cond a b) :=
  _root_.Mips.Fp.f64Compare_spec cond a b

theorem f32Abs_spec (x : BitVec 32) :
    Mips.Fp.binary32.SignOpSpec true x.toNat (Mips.Fp.f32Abs x).toNat :=
  _root_.Mips.Fp.f32Abs_spec x

theorem f32Neg_spec (x : BitVec 32) :
    Mips.Fp.binary32.SignOpSpec false x.toNat (Mips.Fp.f32Neg x).toNat :=
  _root_.Mips.Fp.f32Neg_spec x

theorem f64Abs_spec (x : BitVec 64) :
    Mips.Fp.binary64.SignOpSpec true x.toNat (Mips.Fp.f64Abs x).toNat :=
  _root_.Mips.Fp.f64Abs_spec x

theorem f64Neg_spec (x : BitVec 64) :
    Mips.Fp.binary64.SignOpSpec false x.toNat (Mips.Fp.f64Neg x).toNat :=
  _root_.Mips.Fp.f64Neg_spec x

theorem fpUpdate_spec (fcsr : BitVec 32) (fl : Mips.Fp.Flags) :
    Mips.Fp.FcsrSpec fcsr fl (Mips.Fp.fpUpdate fcsr fl).1 (Mips.Fp.fpUpdate fcsr fl).2 :=
  _root_.Mips.Fp.fpUpdate_spec fcsr fl

theorem fcsrSpec_unique {old : BitVec 32} {fl : Mips.Fp.Flags} {n1 n2 : BitVec 32} {t1 t2 : Bool}
    (h1 : Mips.Fp.FcsrSpec old fl n1 t1) (h2 : Mips.Fp.FcsrSpec old fl n2 t2) : n1 = n2 ∧ t1 = t2 :=
  _root_.Mips.Fp.fcsrSpec_unique h1 h2

theorem exceptionEntry_badInstr (s : State) (code ce : W32) :
    (exceptionEntry s code ce).cp0BadInstr = faultingInstr s ∧
      (exceptionEntry s code ce).cp0BadInstrP =
        (if s.pendingBranch.isSome then instrWordAt s (s.pc - 4#32) else 0#32) :=
  _root_.exceptionEntry_badInstr s code ce

theorem takeInterrupt_badInstr_unchanged (s : State) :
    (takeInterrupt s).cp0BadInstr = s.cp0BadInstr ∧
      (takeInterrupt s).cp0BadInstrP = s.cp0BadInstrP :=
  _root_.takeInterrupt_badInstr_unchanged s

theorem eretnc_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eretnc)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask }) :=
  _root_.eretnc_spec_raw s w hfetch hdecode hpb hcp0 hexec

theorem sigrie_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sigrie code))
    (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) :=
  _root_.sigrie_spec_raw s w code hfetch hdecode hexec

theorem cache_spec_raw (s : State) (w base op off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cache base op off))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match translate s (readReg s (regIdxSpec base) + signExt9 off) with
      | none => takeAddressException s excCodeAdEL (readReg s (regIdxSpec base) + signExt9 off)
      | some _ => { s with pc := s.pc + 4#32 }) :=
  _root_.cache_spec_raw s w base op off hfetch hdecode hpb hcp0 hexec

theorem mfc0_unimplemented_reads_zero (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hnone : cp0Layout .r6 rd.toNat sel.toNat = none) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0#32) with pc := (writeReg s (regIdxSpec rt) 0#32).pc + 4#32 } :=
  _root_.mfc0_unimplemented_reads_zero s w rt rd sel hfetch hdecode hpb hcp0 hexec hnone

theorem mtc0_unimplemented_ignored (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hnone : cp0Layout .r6 rd.toNat sel.toNat = none) :
    step s = timerTick { s with pc := s.pc + 4#32 } :=
  _root_.mtc0_unimplemented_ignored s w rt rd sel hfetch hdecode hpb hcp0 hexec hnone


theorem f32Fma_spec (e : Mips.Fp.Env) (sub : Bool) (c a b : BitVec 32) :
    Mips.Fp.binary32.WithFlushInexact e.flush [c.toNat, a.toNat, b.toNat]
      (Mips.Fp.binary32.FmaSpec e sub (Mips.Fp.binary32.FlushedIn e.flush c.toNat)
        (Mips.Fp.binary32.FlushedIn e.flush a.toNat) (Mips.Fp.binary32.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f32Fma e sub c a b).1.toNat, (Mips.Fp.f32Fma e sub c a b).2) :=
  _root_.Mips.Fp.f32Fma_spec e sub c a b

theorem f64Fma_spec (e : Mips.Fp.Env) (sub : Bool) (c a b : BitVec 64) :
    Mips.Fp.binary64.WithFlushInexact e.flush [c.toNat, a.toNat, b.toNat]
      (Mips.Fp.binary64.FmaSpec e sub (Mips.Fp.binary64.FlushedIn e.flush c.toNat)
        (Mips.Fp.binary64.FlushedIn e.flush a.toNat) (Mips.Fp.binary64.FlushedIn e.flush b.toNat))
      ((Mips.Fp.f64Fma e sub c a b).1.toNat, (Mips.Fp.f64Fma e sub c a b).2) :=
  _root_.Mips.Fp.f64Fma_spec e sub c a b

theorem cmpTable_formula : ∀ (condn : BitVec 5) (r : Mips.Fp.Format.Relation),
    Mips.Fp.cmpCondition condn (decide (r = .un)) (decide (r = .lt)) (decide (r = .eq)) =
      Mips.Fp.cmpHolds condn.toNat r ∧
    (Mips.Fp.cmpTable condn.toNat).2.2.2.2 = (condn.setWidth 4).getLsbD 3 :=
  _root_.Mips.Fp.cmpTable_formula

theorem f32Cmp_spec (condn : BitVec 5) (a b : BitVec 32) :
    Mips.Fp.binary32.CmpSpec condn a.toNat b.toNat (Mips.Fp.f32Cmp condn a b) :=
  _root_.Mips.Fp.f32Cmp_spec condn a b

theorem f64Cmp_spec (condn : BitVec 5) (a b : BitVec 64) :
    Mips.Fp.binary64.CmpSpec condn a.toNat b.toNat (Mips.Fp.f64Cmp condn a b) :=
  _root_.Mips.Fp.f64Cmp_spec condn a b

theorem f32MinMax_spec (op : Mips.Fp.Format.MinMaxOp) (e : Mips.Fp.Env) (a b : BitVec 32) :
    Mips.Fp.binary32.MinMaxSpec op (Mips.Fp.binary32.FlushedIn e.flush a.toNat)
      (Mips.Fp.binary32.FlushedIn e.flush b.toNat)
      ((Mips.Fp.f32MinMax op e a b).1.toNat, (Mips.Fp.f32MinMax op e a b).2) :=
  _root_.Mips.Fp.f32MinMax_spec op e a b

theorem f64MinMax_spec (op : Mips.Fp.Format.MinMaxOp) (e : Mips.Fp.Env) (a b : BitVec 64) :
    Mips.Fp.binary64.MinMaxSpec op (Mips.Fp.binary64.FlushedIn e.flush a.toNat)
      (Mips.Fp.binary64.FlushedIn e.flush b.toNat)
      ((Mips.Fp.f64MinMax op e a b).1.toNat, (Mips.Fp.f64MinMax op e a b).2) :=
  _root_.Mips.Fp.f64MinMax_spec op e a b

theorem f32Class_spec (a : BitVec 32) :
    Mips.Fp.binary32.ClassSpec a.toNat (Mips.Fp.f32Class a).toNat :=
  _root_.Mips.Fp.f32Class_spec a

theorem f64Class_spec (a : BitVec 64) :
    Mips.Fp.binary64.ClassSpec a.toNat (Mips.Fp.f64Class a).toNat :=
  _root_.Mips.Fp.f64Class_spec a

theorem f32Rint_spec (e : Mips.Fp.Env) (a : BitVec 32) :
    Mips.Fp.binary32.RintSpec e a.toNat ((Mips.Fp.f32Rint e a).1.toNat, (Mips.Fp.f32Rint e a).2) :=
  _root_.Mips.Fp.f32Rint_spec e a

theorem f64Rint_spec (e : Mips.Fp.Env) (a : BitVec 64) :
    Mips.Fp.binary64.RintSpec e a.toNat ((Mips.Fp.f64Rint e a).1.toNat, (Mips.Fp.f64Rint e a).2) :=
  _root_.Mips.Fp.f64Rint_spec e a


end Trusted

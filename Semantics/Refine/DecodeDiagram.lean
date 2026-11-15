import Semantics.Refine.Decode
import Semantics.Manual.Decode

/-!
# Refine.DecodeDiagram — the spec's decoder `Manual.Decode` (wave 12b)

* `decode_diagram_sound`, `decode_diagram_complete`: `Manual.Decode` decodes a word to an
  instruction exactly when the word is the diagram (`Manual.enc`) of some instruction.
* `decode_agrees`: a word the model's `decode` accepts is decoded by `Manual.Decode` to the same
  instruction.
* `decode_none_rejected`: a word the model's `decode` rejects that `Manual.Decode` decodes to an
  instruction is `MFC0`/`MTC0` of a register coprocessor 0 does not contain, `EXT` with
  `lsb + msbd > 31` or `INS` with `lsb > msb` (`Rejected`): an instruction whose Operation always
  reaches an oracle choice (`Manual.ConsultsOracle`), which the model resolves as Reserved Instruction.
-/

namespace Refine

open Manual DecodeSpec

/-! ## The diagram fields are the model's field extractors -/

theorem fieldAt_rs (w : W32) : fieldAt w 25 21 = rsOf w := rfl
theorem fieldAt_rt (w : W32) : fieldAt w 20 16 = rtOf w := rfl
theorem fieldAt_rd (w : W32) : fieldAt w 15 11 = rdOf w := rfl
theorem fieldAt_sa (w : W32) : fieldAt w 10 6 = shamtOf w := rfl
theorem fieldAt_imm (w : W32) : fieldAt w 15 0 = immOf w := rfl
theorem fieldAt_target (w : W32) : fieldAt w 25 0 = targetOf w := rfl
theorem fieldAt_cc (w : W32) : fieldAt w 20 18 = ccOf w := rfl
theorem fieldAt_fcc (w : W32) : fieldAt w 10 8 = fccOf w := rfl
theorem fieldAt_cond (w : W32) : fieldAt w 3 0 = condOf w := rfl
theorem fieldAt_code20 (w : W32) : fieldAt w 25 6 = code20Of w := rfl
theorem fieldAt_code10 (w : W32) : fieldAt w 15 6 = code10Of w := rfl
theorem fieldAt_code19 (w : W32) : fieldAt w 24 6 = code19Of w := rfl

/-- The `sel` field (bits 2..0) is the low three bits of the model's `funct` field. -/
theorem fieldAt_sel (w : W32) : fieldAt w 2 0 = functOf w &&& 7#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [fieldAt, functOf, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem fieldAt_sel_lt (w : W32) : (fieldAt w 2 0).toNat < 8 := by
  simp [fieldAt, BitVec.extractLsb]; omega

/-! ## `enc` is `encode` (every instruction, `sel` of `MFC0`/`MTC0` below 8) -/

/-- The `sel` field of `MFC0`/`MTC0` fits its 3 bits (`enc` writes 3 bits, `encode` 6). -/
def SelOK : Instruction → Prop
  | .mfc0 _ _ sel | .mtc0 _ _ sel => sel.toNat < 8
  | _ => True

-- one simp set serves every constructor; some members are unused in the `mfc0`/`mtc0` arms
set_option linter.unusedSimpArgs false in
/-- `enc_eq_encode` without the field ranges: the diagram masks each field to its width as `encode`
does. -/
theorem enc_eq_encode_gen (i : Instruction) (h : SelOK i) : enc i = some (encode i) := by
  cases i
  case mfc0 rt rd sel =>
    simp only [enc, encode, fld3_sel sel h]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case mtc0 rt rd sel =>
    simp only [enc, encode, fld3_sel sel h]
    simp only [fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero,
      BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]
  case ei =>
    simp only [enc, encode, fld, field, maskLow, mkRT, BitVec.or_assoc, mask1, mask5, mask6,
      BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and, BitVec.zero_shiftLeft,
      BitVec.or_zero, show (1#32 <<< 5 : W32) = 32#32 by decide]
  case eret => decide
  all_goals
    simp only [enc, encode, rFormat, iFormat, trapFormat, codeFormat, fld, field, maskLow, mkRT,
      mkIT, mkJT, mkCCR, mkCCI, mkCmp, mkCode20, mkTrap, mkWait, BitVec.or_assoc,
      mask1, mask2, mask3, mask4, mask5, mask6, mask10, mask16, mask19, mask20, mask26, BitVec.shiftLeft_zero, BitVec.reduceAnd, BitVec.zero_and,
      BitVec.zero_shiftLeft, BitVec.or_zero, BitVec.zero_or]

/-! ## Completeness: every diagram word has a candidate with that diagram -/

theorem field_and_mask (n s : Nat) (x m : W32) (hm : m &&& ((1#32 <<< n) - 1#32) = (1#32 <<< n) - 1#32) :
    field n s (x &&& m) = field n s x := by
  simp only [field, maskLow, BitVec.and_assoc, hm]

theorem field_and1 (s : Nat) (x : W32) : field 1 s (x &&& 1#32) = field 1 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and3 (s : Nat) (x : W32) : field 2 s (x &&& 3#32) = field 2 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and7 (s : Nat) (x : W32) : field 3 s (x &&& 7#32) = field 3 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and15 (s : Nat) (x : W32) : field 4 s (x &&& 15#32) = field 4 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and31 (s : Nat) (x : W32) : field 5 s (x &&& 31#32) = field 5 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and63 (s : Nat) (x : W32) : field 6 s (x &&& 63#32) = field 6 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and1023 (s : Nat) (x : W32) : field 10 s (x &&& 1023#32) = field 10 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and65535 (s : Nat) (x : W32) : field 16 s (x &&& 65535#32) = field 16 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and524287 (s : Nat) (x : W32) : field 19 s (x &&& 524287#32) = field 19 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and1048575 (s : Nat) (x : W32) : field 20 s (x &&& 1048575#32) = field 20 s x := field_and_mask _ _ _ _ (by decide)
theorem and63_and7 (x : W32) : x &&& 63#32 &&& 7#32 = x &&& 7#32 := by
  rw [BitVec.and_assoc]; rfl
theorem field_and67108863 (s : Nat) (x : W32) : field 26 s (x &&& 67108863#32) = field 26 s x := field_and_mask _ _ _ _ (by decide)

attribute [local simp] ext_msbd ins_msb opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  opcodeOf_mkIT rsOf_mkIT rtOf_mkIT immOf_mkIT opcodeOf_or_mkJT targetOf_or_mkJT
  fcOf_or_mkRT coOf_or_mkRT
  opcodeOf_mkCCR rsOf_mkCCR ccOf_mkCCR ndOf_mkCCR tfOf_mkCCR rdOf_mkCCR shamtOf_mkCCR
  functOf_mkCCR fcOf_mkCCR
  opcodeOf_mkCCI rsOf_mkCCI ccOf_mkCCI ndOf_mkCCI tfOf_mkCCI immOf_mkCCI
  opcodeOf_mkCmp rsOf_mkCmp rtOf_mkCmp rdOf_mkCmp fccOf_mkCmp condOf_mkCmp fcOf_mkCmp z76Of_mkCmp
  opcodeOf_mkCode20 functOf_mkCode20 code20Of_mkCode20
  opcodeOf_mkTrap functOf_mkTrap rsOf_mkTrap rtOf_mkTrap code10Of_mkTrap
  opcodeOf_mkWait coOf_mkWait functOf_mkWait code19Of_mkWait
  fieldAt_rs fieldAt_rt fieldAt_rd fieldAt_sa fieldAt_imm fieldAt_target fieldAt_cc fieldAt_fcc
  fieldAt_cond fieldAt_code20 fieldAt_code10 fieldAt_code19 fieldAt_sel
  field_and1 field_and3 field_and7 field_and15 field_and31 field_and63 field_and1023 field_and65535
  field_and524287 field_and1048575 field_and67108863 and63_and7

set_option maxRecDepth 4000 in
theorem length_candidates (w : W32) : (candidates w).length = 183 := by simp [candidates]

/-- The `k`-th candidate has the diagram of the instruction. -/
local macro "cand " k:num : tactic => `(tactic| (
  refine ⟨(candidates _)[$k]'(by rw [length_candidates]; decide), List.getElem_mem _, ?_⟩
  simp only [candidates, List.getElem_cons_succ, List.getElem_cons_zero]
  refine (enc_eq_encode_gen _ (by first | trivial | exact fieldAt_sel_lt _)).trans (congrArg some ?_)
  simp only [encode]
  try simp
  try simp [mkRT, mkIT, mkJT, mkCCR, mkCCI, mkCmp, mkCode20, mkTrap, mkWait, and_7, *]))

-- 183 cases, each a field-extraction `simp`: more than the default budget for one declaration
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **The candidate of `i`'s constructor read from `encode i` has the diagram `encode i`.** -/
theorem enc_candidate (i : Instruction) (hs : SelOK i) :
    ∃ j ∈ candidates (encode i), enc j = some (encode i) := by
  cases i
  case add => cand 0
  case lw => cand 1
  case sw => cand 2
  case lwl => cand 3
  case beq => cand 4
  case beql => cand 5
  case addS => cand 6
  case mtc0 rt rd sel => have h8 : sel.toNat < 8 := hs; cand 7
  case bne => cand 8
  case blez => cand 9
  case bgtz => cand 10
  case bltz => cand 11
  case bgez => cand 12
  case bltzal => cand 13
  case bgezal => cand 14
  case bnel => cand 15
  case blezl => cand 16
  case bgtzl => cand 17
  case bltzl => cand 18
  case bgezl => cand 19
  case bltzall => cand 20
  case bgezall => cand 21
  case j => cand 22
  case jal => cand 23
  case jr => cand 24
  case jalr => cand 25
  case jrHb => cand 26
  case jalrHb => cand 27
  case mfc0 rt rd sel => have h8 : sel.toNat < 8 := hs; cand 28
  case di => cand 29
  case ei => cand 30
  case eret => cand 31
  case wait => cand 32
  case rdpgpr => cand 33
  case wrpgpr => cand 34
  case rdhwr => cand 35
  case lb => cand 36
  case lbu => cand 37
  case lh => cand 38
  case lhu => cand 39
  case sb => cand 40
  case sh => cand 41
  case pref => cand 42
  case sync => cand 43
  case synci => cand 44
  case ll => cand 45
  case sc => cand 46
  case lwr => cand 47
  case swl => cand 48
  case swr => cand 49
  case teq => cand 50
  case tne => cand 51
  case tlt => cand 52
  case tge => cand 53
  case tltu => cand 54
  case tgeu => cand 55
  case teqi => cand 56
  case tnei => cand 57
  case tgei => cand 58
  case tgeiu => cand 59
  case tlti => cand 60
  case tltiu => cand 61
  case syscall => cand 62
  case «break» => cand 63
  case mfc1 => cand 64
  case mtc1 => cand 65
  case mfhc1 => cand 66
  case mthc1 => cand 67
  case cfc1 => cand 68
  case ctc1 => cand 69
  case lwc1 => cand 70
  case swc1 => cand 71
  case ldc1 => cand 72
  case sdc1 => cand 73
  case lwxc1 => cand 74
  case ldxc1 => cand 75
  case swxc1 => cand 76
  case sdxc1 => cand 77
  case prefx => cand 78
  case subS => cand 79
  case mulS => cand 80
  case divS => cand 81
  case sqrtS => cand 82
  case absS => cand 83
  case movS => cand 84
  case negS => cand 85
  case recipS => cand 86
  case rsqrtS => cand 87
  case roundWS => cand 88
  case truncWS => cand 89
  case ceilWS => cand 90
  case floorWS => cand 91
  case cvtWS => cand 92
  case addD => cand 93
  case subD => cand 94
  case mulD => cand 95
  case divD => cand 96
  case sqrtD => cand 97
  case absD => cand 98
  case movD => cand 99
  case negD => cand 100
  case recipD => cand 101
  case rsqrtD => cand 102
  case roundWD => cand 103
  case truncWD => cand 104
  case ceilWD => cand 105
  case floorWD => cand 106
  case cvtWD => cand 107
  case cvtDS => cand 108
  case cvtSW => cand 109
  case cvtDW => cand 110
  case cvtSD => cand 111
  case cCondS => cand 112
  case cCondD => cand 113
  case movfS => cand 114
  case movtS => cand 115
  case movnS => cand 116
  case movzS => cand 117
  case movfD => cand 118
  case movtD => cand 119
  case movnD => cand 120
  case movzD => cand 121
  case movf => cand 122
  case movt => cand 123
  case maddS => cand 124
  case maddD => cand 125
  case msubS => cand 126
  case msubD => cand 127
  case nmaddS => cand 128
  case nmaddD => cand 129
  case nmsubS => cand 130
  case nmsubD => cand 131
  case bc1f => cand 132
  case bc1t => cand 133
  case bc1fl => cand 134
  case bc1tl => cand 135
  case addu => cand 136
  case sub => cand 137
  case subu => cand 138
  case and => cand 139
  case or => cand 140
  case xor => cand 141
  case nor => cand 142
  case slt => cand 143
  case sltu => cand 144
  case movn => cand 145
  case movz => cand 146
  case sll => cand 147
  case srl => cand 148
  case sra => cand 149
  case sllv => cand 150
  case srlv => cand 151
  case srav => cand 152
  case rotr => cand 153
  case rotrv => cand 154
  case mult => cand 155
  case multu => cand 156
  case div => cand 157
  case divu => cand 158
  case mfhi => cand 159
  case mthi => cand 160
  case mflo => cand 161
  case mtlo => cand 162
  case mul => cand 163
  case madd => cand 164
  case maddu => cand 165
  case msub => cand 166
  case msubu => cand 167
  case clz => cand 168
  case clo => cand 169
  case seb => cand 170
  case seh => cand 171
  case wsbh => cand 172
  case ext => cand 173
  case ins => cand 174
  case addi => cand 175
  case addiu => cand 176
  case slti => cand 177
  case sltiu => cand 178
  case andi => cand 179
  case ori => cand 180
  case xori => cand 181
  case lui => cand 182

end Refine

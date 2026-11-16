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
theorem fieldAt_off9 (w : W32) : fieldAt w 15 7 = off9Of w := rfl
theorem fieldAt_code20 (w : W32) : fieldAt w 25 6 = code20Of w := rfl
theorem fieldAt_code10 (w : W32) : fieldAt w 15 6 = code10Of w := rfl
theorem fieldAt_code19 (w : W32) : fieldAt w 24 6 = code19Of w := rfl
theorem fieldAt_sa2 (w : W32) : fieldAt w 7 6 = sa2Of w := rfl
theorem fieldAt_imm19 (w : W32) : fieldAt w 18 0 = imm19Of w := rfl

/-- The `sel` field (bits 2..0) is the low three bits of the model's `funct` field. -/
theorem fieldAt_sel (w : W32) : fieldAt w 2 0 = functOf w &&& 7#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [fieldAt, functOf, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The `condn` field of CMP.condn.fmt (bits 4..0) is the low five bits of the model's `funct`. -/
theorem fieldAt_40 (w : W32) : fieldAt w 4 0 = functOf w &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [fieldAt, functOf, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem and63_and31 (x : W32) : x &&& 63#32 &&& 31#32 = x &&& 31#32 := by
  rw [BitVec.and_assoc]; rfl

theorem fieldAt_sel_lt (w : W32) : (fieldAt w 2 0).toNat < 8 := by
  simp [fieldAt, BitVec.extractLsb]; omega

/-- The `sel` field of `RDHWR` (bits 8..6) is the low three bits of the model's `sa` field. -/
theorem fieldAt_sel86 (w : W32) : fieldAt w 8 6 = shamtOf w &&& 7#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [fieldAt, shamtOf, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem fieldAt_sel86_lt (w : W32) : (fieldAt w 8 6).toNat < 8 := by
  simp [fieldAt, BitVec.extractLsb]; omega

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
theorem field_and511 (s : Nat) (x : W32) : field 9 s (x &&& 511#32) = field 9 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and1023 (s : Nat) (x : W32) : field 10 s (x &&& 1023#32) = field 10 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and65535 (s : Nat) (x : W32) : field 16 s (x &&& 65535#32) = field 16 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and524287 (s : Nat) (x : W32) : field 19 s (x &&& 524287#32) = field 19 s x := field_and_mask _ _ _ _ (by decide)
theorem field_and1048575 (s : Nat) (x : W32) : field 20 s (x &&& 1048575#32) = field 20 s x := field_and_mask _ _ _ _ (by decide)
theorem and63_and7 (x : W32) : x &&& 63#32 &&& 7#32 = x &&& 7#32 := by
  rw [BitVec.and_assoc]; rfl
theorem and31_and7 (x : W32) : x &&& 31#32 &&& 7#32 = x &&& 7#32 := by
  rw [BitVec.and_assoc]; rfl
theorem field_and67108863 (s : Nat) (x : W32) : field 26 s (x &&& 67108863#32) = field 26 s x := field_and_mask _ _ _ _ (by decide)

attribute [local simp] ext_msbd ins_msb opcodeOf_or_mkRT rsOf_or_mkRT rtOf_or_mkRT rdOf_or_mkRT shamtOf_or_mkRT
  functOf_or_mkRT opcodeOf_mkRT rsOf_mkRT rtOf_mkRT rdOf_mkRT shamtOf_mkRT functOf_mkRT
  opcodeOf_mkIT rsOf_mkIT rtOf_mkIT immOf_mkIT opcodeOf_or_mkJT targetOf_or_mkJT
  coOf_or_mkRT
  opcodeOf_or_mkOff9 rsOf_or_mkOff9 rtOf_or_mkOff9 off9Of_or_mkOff9 bit6Of_or_mkOff9 functOf_or_mkOff9
  opcodeOf_mkCode20 functOf_mkCode20 code20Of_mkCode20
  opcodeOf_mkTrap functOf_mkTrap rsOf_mkTrap rtOf_mkTrap code10Of_mkTrap
  opcodeOf_mkWait coOf_mkWait functOf_mkWait code19Of_mkWait
  fieldAt_rs fieldAt_rt fieldAt_rd fieldAt_sa fieldAt_imm fieldAt_target fieldAt_off9
  fieldAt_code20 fieldAt_code10 fieldAt_code19 fieldAt_sel fieldAt_sel86
  field_and1 field_and3 field_and7 field_and15 field_and31 field_and63 field_and511 field_and1023
  field_and65535
  field_and524287 field_and1048575 field_and67108863 and63_and7 and31_and7
  opcodeOf_or_mkRT2 rsOf_or_mkRT2 rtOf_or_mkRT2 rdOf_or_mkRT2 sa3Of_or_mkRT2 sa2Of_or_mkRT2
  functOf_or_mkRT2 opcodeOf_mkRT2 rsOf_mkRT2 rtOf_mkRT2 rdOf_mkRT2 sa3Of_mkRT2
  sa2Of_mkRT2 functOf_mkRT2 opcodeOf_or_mkPc19 rsOf_or_mkPc19 pcrelOf_or_mkPc19 imm19Of_or_mkPc19
  fieldAt_sa2 fieldAt_imm19

set_option maxRecDepth 4000 in
theorem length_candidates (w : W32) : (candidates w).length = 203 := rfl

/-- Pick the `k`-th entry of `candidates w` as the witness and reduce it (`whnf`, one step per list
cell) to the constructor it is, e.g. `.add (fieldAt w 25 21) ..`. Unfolding the 203-entry list with
`simp` instead costs one rewrite of the whole list per cell. -/
local macro "candidate_at " k:num : tactic => `(tactic| (
  refine ⟨(candidates _)[$k]'(by rw [length_candidates]; decide), List.getElem_mem _, ?_⟩
  conv => lhs; arg 1; whnf))

/-- Read the operand fields back out of an encoded word: `fieldAt (encode i) hi lo` is the operand
`encode` wrote there, masked to the field width. -/
local macro "read_fields" : tactic => `(tactic|
  simp only [fieldAt_rs, fieldAt_rt, fieldAt_rd, fieldAt_sa, fieldAt_imm, fieldAt_target,
    fieldAt_off9, fieldAt_code20, fieldAt_code10, fieldAt_code19, fieldAt_sel, fieldAt_sel86,
    fieldAt_sa2, fieldAt_imm19, ext_msbd, ins_msb,
    rsOf_mkRT, rtOf_mkRT, rdOf_mkRT, shamtOf_mkRT, rsOf_or_mkRT, rtOf_or_mkRT, rdOf_or_mkRT,
    shamtOf_or_mkRT, functOf_or_mkRT, rsOf_mkIT, rtOf_mkIT, immOf_mkIT, targetOf_or_mkJT,
    rsOf_or_mkOff9, rtOf_or_mkOff9, off9Of_or_mkOff9, code20Of_mkCode20, rsOf_mkTrap, rtOf_mkTrap,
    code10Of_mkTrap, code19Of_mkWait, rsOf_mkRT2, rtOf_mkRT2, rdOf_mkRT2, sa2Of_mkRT2,
    rsOf_or_mkRT2, rtOf_or_mkRT2, rdOf_or_mkRT2, sa2Of_or_mkRT2, rsOf_or_mkPc19, imm19Of_or_mkPc19,
    and63_and7, and31_and7, BitVec.reduceAnd, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
    BitVec.zero_or])

/-- Masking a field twice is masking it once: `field n s (x &&& mask n) = field n s x`, after
unfolding the format builders. The hypotheses (`sel.toNat < 8`) feed `and_7`. -/
local macro "masks_idem" : tactic => `(tactic|
  simp only [mkRT, mkIT, mkJT, mkOff9, mkCode20, mkTrap, mkWait, mkRT2, mkPc19, and_7,
    field_and3, field_and31, field_and511, field_and1023, field_and65535, field_and524287,
    field_and1048575, field_and67108863, *])

/-- The `k`-th candidate has the diagram of the instruction: `enc` of it is `encode` of it
(`enc_eq_encode_gen`), and `encode` of it is `encode i` (read the fields back, drop the masks). -/
local macro "cand " k:num : tactic => `(tactic| (
  candidate_at $k
  refine (enc_eq_encode_gen _ (by first | trivial | exact fieldAt_sel_lt _ | exact fieldAt_sel86_lt _)).trans (congrArg some ?_)
  simp only [encode, cop1R]
  try read_fields
  try masks_idem))

/-- A register field masked to its 5 bits is the same register. -/
theorem reg_and31 (x : W32) : reg (x &&& 31#32) = reg x := by
  apply Fin.ext
  simp only [reg_val, BitVec.toNat_and, show (31#32).toNat = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem fieldAt_off21 (w : W32) : fieldAt w 20 0 = off21Of w := rfl

set_option hygiene false in
/-- The `k`-th candidate has the diagram of the compact branch: its constraint is that of the
instruction (`hs`), its word the instruction's. -/
local macro "cand_cb " k:num : tactic => `(tactic| (
  candidate_at $k
  refine (enc_eq_encode_gen _ ?_).trans (congrArg some ?_)
  · simp only [SelOK, encode, fieldAt_rs, fieldAt_rt, fieldAt_imm, fieldAt_off21, rsOf_mkIT, rtOf_mkIT,
      rsOf_mkOff21, reg_and31] at hs ⊢
    exact hs
  · simp only [encode, fieldAt_rs, fieldAt_rt, fieldAt_imm, fieldAt_off21, rsOf_mkIT, rtOf_mkIT,
      immOf_mkIT, rsOf_mkOff21, off21Of_mkOff21]
    simp [mkIT, mkOff21, field, maskLow, BitVec.and_assoc]))

-- 203 cases, each a field-extraction `simp`: more than the default budget for one declaration
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **The candidate of `i`'s constructor read from `encode i` has the diagram `encode i`.** -/
theorem enc_candidate (i : Instruction) (hs : SelOK i) :
    ∃ j ∈ candidates (encode i), enc j = some (encode i) := by
  cases i
  case pause => cand 0
  case add => cand 1
  case lw => cand 2
  case sw => cand 3
  case beq => cand 4
  case addS => cand 5
  case mtc0 rt rd sel => have h8 : sel.toNat < 8 := hs; cand 6
  case bne => cand 7
  case blez => cand 8
  case bgtz => cand 9
  case bltz => cand 10
  case bgez => cand 11
  case j => cand 12
  case jal => cand 13
  case jalr => cand 14
  case jalrHb => cand 15
  case mfc0 rt rd sel => have h8 : sel.toNat < 8 := hs; cand 16
  case di => cand 17
  case ei => cand 18
  case eret => cand 19
  case wait => cand 20
  case rdpgpr => cand 21
  case wrpgpr => cand 22
  case rdhwr rt rd sel => have h8 : sel.toNat < 8 := hs; cand 23
  case lb => cand 24
  case lbu => cand 25
  case lh => cand 26
  case lhu => cand 27
  case sb => cand 28
  case sh => cand 29
  case pref => cand 30
  case sync => cand 31
  case synci => cand 32
  case ll => cand 33
  case sc => cand 34
  case teq => cand 35
  case tne => cand 36
  case tlt => cand 37
  case tge => cand 38
  case tltu => cand 39
  case tgeu => cand 40
  case syscall => cand 41
  case «break» => cand 42
  case mfc1 => cand 43
  case mtc1 => cand 44
  case mfhc1 => cand 45
  case mthc1 => cand 46
  case cfc1 => cand 47
  case ctc1 => cand 48
  case lwc1 => cand 49
  case swc1 => cand 50
  case ldc1 => cand 51
  case sdc1 => cand 52
  case subS => cand 53
  case mulS => cand 54
  case divS => cand 55
  case sqrtS => cand 56
  case absS => cand 57
  case movS => cand 58
  case negS => cand 59
  case recipS => cand 60
  case rsqrtS => cand 61
  case roundWS => cand 62
  case truncWS => cand 63
  case ceilWS => cand 64
  case floorWS => cand 65
  case cvtWS => cand 66
  case addD => cand 67
  case subD => cand 68
  case mulD => cand 69
  case divD => cand 70
  case sqrtD => cand 71
  case absD => cand 72
  case movD => cand 73
  case negD => cand 74
  case recipD => cand 75
  case rsqrtD => cand 76
  case roundWD => cand 77
  case truncWD => cand 78
  case ceilWD => cand 79
  case floorWD => cand 80
  case cvtWD => cand 81
  case cvtDS => cand 82
  case cvtSW => cand 83
  case cvtDW => cand 84
  case cvtSD => cand 85
  case addu => cand 86
  case sub => cand 87
  case subu => cand 88
  case and => cand 89
  case or => cand 90
  case xor => cand 91
  case nor => cand 92
  case slt => cand 93
  case sltu => cand 94
  case sll => cand 95
  case srl => cand 96
  case sra => cand 97
  case sllv => cand 98
  case srlv => cand 99
  case srav => cand 100
  case rotr => cand 101
  case rotrv => cand 102
  case clz => cand 103
  case clo => cand 104
  case seb => cand 105
  case seh => cand 106
  case wsbh => cand 107
  case ext => cand 108
  case ins => cand 109
  case addiu => cand 110
  case slti => cand 111
  case sltiu => cand 112
  case andi => cand 113
  case ori => cand 114
  case xori => cand 115
  case aui => cand 116
  case nal => cand 117
  case bal => cand 118
  case eretnc => cand 119
  case sigrie => cand 120
  case cache => cand 121
  case mul => cand 122
  case muh => cand 123
  case mulu => cand 124
  case muhu => cand 125
  case div => cand 126
  case mod => cand 127
  case divu => cand 128
  case modu => cand 129
  case seleqz => cand 130
  case selnez => cand 131
  case lsa => cand 132
  case align => cand 133
  case bitswap => cand 134
  case addiupc => cand 135
  case lwpc => cand 136
  case auipc => cand 137
  case aluipc => cand 138
  case bc => cand 139
  case balc => cand 140
  case beqc => cand_cb 141
  case bnec => cand_cb 142
  case bltc => cand_cb 143
  case bgec => cand_cb 144
  case bltuc => cand_cb 145
  case bgeuc => cand_cb 146
  case blezc => cand_cb 147
  case bgezc => cand_cb 148
  case bgtzc => cand_cb 149
  case bltzc => cand_cb 150
  case beqzc => cand_cb 151
  case bnezc => cand_cb 152
  case blezalc => cand_cb 153
  case bgezalc => cand_cb 154
  case bgtzalc => cand_cb 155
  case bltzalc => cand_cb 156
  case beqzalc => cand_cb 157
  case bnezalc => cand_cb 158
  case bovc => cand_cb 159
  case bnvc => cand_cb 160
  case jic => cand 161
  case jialc => cand 162
  case roundLS => cand 163
  case roundLD => cand 164
  case truncLS => cand 165
  case truncLD => cand 166
  case ceilLS => cand 167
  case ceilLD => cand 168
  case floorLS => cand 169
  case floorLD => cand 170
  case cvtLS => cand 171
  case cvtLD => cand 172
  case cvtSL => cand 173
  case cvtDL => cand 174
  case cmpS cond fd fs ft =>
    have hlt := DecodeSpec.cmpCondnOK_lt ((cmpCondnOK_eq cond).trans hs)
    have e : cond &&& 63#32 &&& 31#32 = cond := by rw [and63_and31]; exact and_31 _ (by omega)
    candidate_at 175
    have hf : fieldAt (encode (.cmpS cond fd fs ft)) 4 0 = cond := by
      simp only [encode, cop1R, fieldAt_40, functOf_or_mkRT]
      rw [show (17#32 <<< 26 &&& 63#32 : W32) = 0#32 by decide, BitVec.zero_or, e]
    rw [hf]
    refine (enc_eq_encode_gen _ (by exact hs)).trans (congrArg some ?_)
    simp only [encode, cop1R]
    try simp
    try simp [mkRT, and_7, *]
  case cmpD cond fd fs ft =>
    have hlt := DecodeSpec.cmpCondnOK_lt ((cmpCondnOK_eq cond).trans hs)
    have e : cond &&& 63#32 &&& 31#32 = cond := by rw [and63_and31]; exact and_31 _ (by omega)
    candidate_at 176
    have hf : fieldAt (encode (.cmpD cond fd fs ft)) 4 0 = cond := by
      simp only [encode, cop1R, fieldAt_40, functOf_or_mkRT]
      rw [show (17#32 <<< 26 &&& 63#32 : W32) = 0#32 by decide, BitVec.zero_or, e]
    rw [hf]
    refine (enc_eq_encode_gen _ (by exact hs)).trans (congrArg some ?_)
    simp only [encode, cop1R]
    try simp
    try simp [mkRT, and_7, *]
  case bc1eqz => cand 177
  case bc1nez => cand 178
  case selS => cand 179
  case selD => cand 180
  case seleqzS => cand 181
  case seleqzD => cand 182
  case selnezS => cand 183
  case selnezD => cand 184
  case maddfS => cand 185
  case maddfD => cand 186
  case msubfS => cand 187
  case msubfD => cand 188
  case maxS => cand 197
  case maxD => cand 198
  case minS => cand 193
  case minD => cand 194
  case maxaS => cand 199
  case maxaD => cand 200
  case minaS => cand 195
  case minaD => cand 196
  case classS => cand 191
  case classD => cand 192
  case rintS => cand 189
  case rintD => cand 190
  case dvp => cand 201
  case evp => cand 202

end Refine

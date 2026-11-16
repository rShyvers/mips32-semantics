import Semantics.Instruction

/-!
# WellFormed — the field-range side condition of the decode/encode round trip

`Instruction.WellFormed` appears in the *statement* of `decode_encode`
(`Semantics/Specs/DecodeSpec.lean`), so it is kept apart from the proofs: it is imported by
`Semantics/Specs/Defs.lean` (statement vocabulary) and hence by the statements-only
`Semantics/Statements.lean`.
-/

/-- Field-range conditions under which `encode` is injective / `decode`
inverts it: register numbers and shift amounts `< 32`, 16-bit immediates
`< 2 ^ 16` (the 9-bit offsets of `ll`/`sc`/`pref`/`cache` `< 2 ^ 9`, the `sel` of `rdhwr`/`mfc0`/`mtc0`
`< 8`, the 19-bit immediates of `addiupc`/`lwpc` `< 2 ^ 19`, the 2-bit `sa`/`bp` of `lsa`/`align`
`< 4`), 26-bit jump targets `< 2 ^ 26`; `ext`/`ins` need a non-empty
bitfield inside the word; `sll $0,$0,5` is
not an `sll` but `pause` (MD00086 Vol II-A Rev 6.06, PAUSE, p.317). -/
def Instruction.WellFormed : Instruction → Prop
  | .add rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .addu rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .sub rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .subu rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .and rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .or rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .xor rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .nor rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .slt rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .sltu rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .sll rd rt shamt => rd.toNat < 32 ∧ rt.toNat < 32 ∧ shamt.toNat < 32 ∧
      ¬(rd = 0#32 ∧ rt = 0#32 ∧ shamt = 5#32)
  | .pause => True
  | .srl rd rt shamt => rd.toNat < 32 ∧ rt.toNat < 32 ∧ shamt.toNat < 32
  | .sra rd rt shamt => rd.toNat < 32 ∧ rt.toNat < 32 ∧ shamt.toNat < 32
  | .sllv rd rt rs => rd.toNat < 32 ∧ rt.toNat < 32 ∧ rs.toNat < 32
  | .srlv rd rt rs => rd.toNat < 32 ∧ rt.toNat < 32 ∧ rs.toNat < 32
  | .srav rd rt rs => rd.toNat < 32 ∧ rt.toNat < 32 ∧ rs.toNat < 32
  | .rotr rd rt sa => rd.toNat < 32 ∧ rt.toNat < 32 ∧ sa.toNat < 32
  | .rotrv rd rt rs => rd.toNat < 32 ∧ rt.toNat < 32 ∧ rs.toNat < 32
  | .jalr rs rd => rs.toNat < 32 ∧ rd.toNat < 32
  | .jalrHb rs rd => rs.toNat < 32 ∧ rd.toNat < 32
  | .clo rs rd => rs.toNat < 32 ∧ rd.toNat < 32
  | .clz rs rd => rs.toNat < 32 ∧ rd.toNat < 32
  | .seb rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .seh rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .wsbh rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .ext rt rs pos size => rt.toNat < 32 ∧ rs.toNat < 32 ∧ pos.toNat < 32 ∧ 1 ≤ size.toNat ∧ pos.toNat + size.toNat ≤ 32
  | .ins rt rs pos size => rt.toNat < 32 ∧ rs.toNat < 32 ∧ pos.toNat < 32 ∧ 1 ≤ size.toNat ∧ pos.toNat + size.toNat ≤ 32
  | .rdhwr rt rd sel => rt.toNat < 32 ∧ rd.toNat < 32 ∧ sel.toNat < 8
  | .addiu rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .slti rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .sltiu rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .andi rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .ori rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .xori rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .aui rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  -- BEGIN R6-4
  | .mul rs rt rd | .muh rs rt rd | .mulu rs rt rd | .muhu rs rt rd
  | .div rs rt rd | .mod rs rt rd | .divu rs rt rd | .modu rs rt rd
  | .seleqz rs rt rd | .selnez rs rt rd => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32
  | .lsa rs rt rd sa => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32 ∧ sa.toNat < 4
  | .align rs rt rd bp => rs.toNat < 32 ∧ rt.toNat < 32 ∧ rd.toNat < 32 ∧ bp.toNat < 4
  | .bitswap rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .addiupc rs imm | .lwpc rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 19
  | .auipc rs imm | .aluipc rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  -- END R6-4
  | .lw rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .sw rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .lb rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .lbu rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .lh rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .lhu rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .sh rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .sb rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .ll rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 9
  | .sc rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 9
  | .beq rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .bne rs rt imm => rs.toNat < 32 ∧ rt.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .blez rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .bgtz rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .bltz rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .bgez rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .nal imm => imm.toNat < 2 ^ 16
  | .bal imm => imm.toNat < 2 ^ 16
  | .synci rs imm => rs.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .j target => target.toNat < 2 ^ 26
  | .jal target => target.toNat < 2 ^ 26
  | .syscall code => code.toNat < 2 ^ 20
  | .teq rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .tne rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .tlt rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .tge rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .tltu rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .tgeu rs rt code => rs.toNat < 32 ∧ rt.toNat < 32 ∧ code.toNat < 2 ^ 10
  | .break code => code.toNat < 2 ^ 20
  | .sync stype => stype.toNat < 32
  | .pref rs hint imm => rs.toNat < 32 ∧ hint.toNat < 32 ∧ imm.toNat < 2 ^ 9
  | .mfc0 rt rd sel => rt.toNat < 32 ∧ rd.toNat < 32 ∧ sel.toNat < 8
  | .mtc0 rt rd sel => rt.toNat < 32 ∧ rd.toNat < 32 ∧ sel.toNat < 8
  | .di rt => rt.toNat < 32
  | .ei rt => rt.toNat < 32
  | .eret => True
  | .wait code => code.toNat < 2 ^ 19
  | .rdpgpr rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .wrpgpr rd rt => rd.toNat < 32 ∧ rt.toNat < 32
  | .mfc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .mtc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .lwc1 rs ft imm => rs.toNat < 32 ∧ ft.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .swc1 rs ft imm => rs.toNat < 32 ∧ ft.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .ldc1 rs ft imm => rs.toNat < 32 ∧ ft.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .sdc1 rs ft imm => rs.toNat < 32 ∧ ft.toNat < 32 ∧ imm.toNat < 2 ^ 16
  | .addS fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .subS fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .mulS fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .divS fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .movS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtSW fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtWS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .sqrtS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .absS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .negS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .roundWS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .truncWS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .ceilWS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .floorWS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .addD fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .subD fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .mulD fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .divD fd fs ft => fd.toNat < 32 ∧ fs.toNat < 32 ∧ ft.toNat < 32
  | .movD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtDS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtSD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtDW fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cvtWD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .sqrtD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .absD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .negD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .cfc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .ctc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .mfhc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .mthc1 rt fs => rt.toNat < 32 ∧ fs.toNat < 32
  | .recipS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .rsqrtS fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .recipD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .rsqrtD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .roundWD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .truncWD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .ceilWD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  | .floorWD fd fs => fd.toNat < 32 ∧ fs.toNat < 32
  -- BEGIN R6-2
  | .eretnc => True
  | .sigrie code => code.toNat < 2 ^ 16
  | .cache base op off => base.toNat < 32 ∧ op.toNat < 32 ∧ off.toNat < 2 ^ 9
  -- END R6-2

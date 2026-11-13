import Semantics.Word
import Semantics.Types

/-!
# Instruction — the modeled MIPS32r2 instruction set, decode, and encode

Depends only on `Word` and `Types`. Ground truth for every encoding below is
`docs/spec/INSTRUCTION-REF.md`, which summarises the manuals; the latest
revisions in `docs/spec/manuals/` are normative, read for the pre-Release-6
wording (MD00086 Vol II-A Rev 6.06; see CLAUDE.md). Comments below that cite
"MD00086 Rev 2.50" with a table or page number are historical citations of
that older revision.

All instruction variants carry their **raw** field values as `W32`s (not yet
sign/zero-extended, not yet interpreted as signed shift amounts, etc.) — the
`Step.lean` is responsible for applying `signExt16` / `zeroExt16` /
`.toNat` / `.toInt` as each instruction's semantics require. This keeps
`decode`/`encode` a pure, total, reversible bit-layout transformation with no
semantic interpretation baked in.

Field-shape summary (see each constructor's docstring for details):
- R-type reg/reg/reg (`rs rt rd`): `add addu sub subu and or xor nor slt sltu
  movn movz` — `movn`/`movz` share the exact add/sub field shape but write
  `$rd` only conditionally on `$rt`.
- R-type shift (`rd rt shamt`): `sll srl sra` — note `rs` is unused/ignored.
- R-type variable shift (`rd rt rs`), MIPS32 (opcode 0, funct 0x04/0x06/0x07):
  `sllv srlv srav` — the shift amount is the *register* `$rs`'s low 5 bits
  (masked at execution time by `Step`), not a fixed `shamt` field; `shamt`
  itself is unused/fixed 0 in the encoding (v1.x addition; see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.4).
- R-type mult/div (`rs rt`): `mult multu div divu` — `rd`/`shamt` unused.
- R-type move (`rd`): `mflo mfhi` — `rs`/`rt`/`shamt` unused.
- R-type move, write direction (`rs`): `mthi mtlo` — `rt`/`rd`/`shamt`
  unused; the write-direction counterparts to `mfhi`/`mflo` above (MIPS32
  addition; see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5), needed for OS
  context switching and setjmp/longjmp to save/restore `hi`/`lo`.
- R-type multiply-accumulate (`rs rt`), SPECIAL2 (opcode 0x1c): `madd
  maddu msub msubu` — same `rs rt` shape as `mult`/`multu` (`rd`/`shamt`
  unused), accumulating into (or subtracting from) the *existing* `hi`/`lo`
  pair rather than overwriting it (MIPS32 addition; see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
- R-type jump register (`rs`): `jr` — `rt`/`rd`/`shamt` unused. (`rs rd`): `jalr`
  — `rt`/`shamt` unused. Real MIPS32 register-indirect jump/call (MD00086
  §3.2); like `j`/`jal`, these get the standard one-instruction delay slot
  via `pendingBranch`, but the target comes from a register read instead of
  the 26-bit `target` field.
- R-type bit-count (`rs rd`), SPECIAL2 (opcode 0x1c): `clo clz` — the raw 32-bit
  encoding's `rt` field duplicates `rd` (a real MIPS32 hardware quirk; see each
  constructor's docstring), so it is not modeled as a separate `Instruction`
  field.
- R-type GPR multiply (`rs rt rd`), SPECIAL2 (opcode 0x1c, funct 0x02): `mul`
  — same `rs rt rd` field shape as `add`, but SPECIAL2-opcoded like `clo`/
  `clz`; writes the low 32 bits of the signed product directly to `$rd`
  (v1.x addition; see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
- R-type sign-extend (`rd rt`), SPECIAL3 BSHFL (opcode 0x1f, funct 0x20):
  `seb seh` — `rs` unused/fixed 0; distinguished from each other (and from
  other BSHFL sub-ops, none of which are in scope here) by the
  shamt-position sub-field (`0x10` for `seb`, `0x18` for `seh`).
- SPECIAL3 `rdhwr` (`rt rd`; opcode 0x1f, funct 0x3b, MIPS32 Release 2): `rs`
  and bits 10..6 must be zero (no Release 6 `sel`).
- I-type arith/logic (`rs rt imm`): `addi addiu slti sltiu andi ori xori`.
- I-type `lui` (`rt imm`): `rs` is unused/fixed 0.
- I-type load/store (`rs rt imm`): `lw sw lb lbu lh lhu sh` — `rs` is the base
  register, `rt` is the destination (loads) or source (stores) register,
  `imm` is the raw 16-bit offset field (not yet sign-extended).
- I-type load-linked/store-conditional (`rs rt imm`), same field shape as
  `lw`/`sw`: `ll sc` — real MIPS32 atomic synchronization primitives (opcodes
  0x30/0x38); not part of the original v1 instruction set, added as the
  `State.llBit` single-hart model (see `Types.lean`'s `llBit` docstring and
  `docs/spec/INSTRUCTION-REF.md`).
- `sync` (`stype`): memory-ordering barrier (opcode 0, funct 0x0f). The
  5-bit `stype` field (bits 10..6) is carried so `encode ∘ decode` is exact;
  every `stype` executes as the same no-op (single hart, no reordering).
- I-type synchronize-caches hint (`rs imm`), same field shape as `blez`:
  `synci` — real MIPS32 instruction-cache-flush hint for self-modifying
  code / JIT compilers (REGIMM opcode 0x01, `rt` field fixed `0x1f`;
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7, MIPS32r2). Computes the same
  `$rs + sext16(offset)` address as `lw`/`sw`, but since this simulator has
  no instruction-cache model at all, the address is never used for
  anything (see `Step.lean`/`docs/spec/INSTRUCTION-REF.md`).
- I-type unaligned load/store (`rs rt imm`), same field shape as `lw`/`sw`:
  `lwl lwr swl swr` — real MIPS32 classic (pre-r6) unaligned memory-access
  pair (opcodes 0x22/0x26/0x2a/0x2e); not part of the original v1
  instruction set (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.6 and
  `docs/spec/INSTRUCTION-REF.md`'s dedicated section). `rs` is the base
  register, `rt` is the dest/src register (also read, since these partially
  preserve `$rt`'s prior value), `imm` is the raw offset field, exactly like
  `lw`/`sw`; unlike `lw`/`sw`, the effective address has no alignment
  requirement at all.
- I-type branch reg/reg (`rs rt imm`): `beq bne`.
- I-type branch reg-only (`rs imm`): `blez bgtz` — `rt` is unused/fixed 0.
- I-type "branch likely" family (same field shapes as their non-likely
  counterparts above): `beql bnel` (`rs rt imm`), `blezl bgtzl bltzl bgezl
  bltzall bgezall` (`rs imm`) — real MIPS32, deprecated in MIPS32 and
  removed in Release 6 (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.3). `decode`/
  `encode` treat these exactly like `beq`/`bltz`/etc.; the one thing that
  actually makes them different (nullifying/squashing a not-taken delay
  slot instead of executing it) is pure `Step.lean` behavior, invisible at
  the field-shape level this module works at.
- J-type (`target`): `j jal` — raw 26-bit target field (not yet shifted/combined
  with `PC_next`'s top 4 bits; that composition is `Step`'s job).
- `syscall` (`code`): the 20-bit `code` field (bits 25..6) is carried but
  ignored by execution; the environment-call number lives in `$v0`.
- R-type trap-on-condition (`rs rt code`; bits 15..6 are a 10-bit `code`
  field, "ignored by hardware"): `teq tne tlt tge tltu tgeu` — real MIPS32 SPECIAL-opcode trap
  family, not part of the original v1 instruction set but added as a
  minimal coprocessor-0 trap/exception model (see `docs/spec/INSTRUCTION-REF.md`
  and `Semantics/Step.lean` for the exception-taken semantics). Ground
  truth is the real MIPS32 ISA (not MARS, which models exceptions only very
  loosely) — funct values are cited per-constructor below.
- `break` (`code`): unconditional Breakpoint exception; the 20-bit `code`
  field (bits 25..6) is carried but has no effect on execution.
- I-type trap-immediate (`rs imm`), REGIMM (opcode 0x01; `rt` field unused by
  the ALU, since it instead selects which trap this is, same multiplexing
  convention as `bltz`/`bgez`/`bltzal`/`bgezal` above): `teqi tnei tgei
  tgeiu tlti tltiu` — real MIPS32 immediate-operand trap family (see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8), the sign-extended-16-bit-immediate
  counterpart of the `teq tne tlt tge tltu tgeu` register-register family
  above; same coprocessor-0 trap/exception model (`takeException` in
  `Semantics/Step.lean`). `tgeiu`/`tltiu` follow the same "sign-extend the
  16-bit immediate to 32 bits, then compare the result as unsigned"
  convention already used by `sltiu`.
- Coprocessor-0 (CP0) instructions — opcode `0x10` (COP0):
  - `mfc0`/`mtc0` (`rt rd sel`): CP0-register ↔ GPR move for the modeled
    `(rd, sel)` pairs (`isModeledCp0Reg`); any other pair, or nonzero bits
    10..3, does not decode (→ Reserved Instruction).
  - `di`/`ei` (`rt`): `$rt ← Status`, then `Status.IE ← 0`/`1` (Release 2).
  - `eret` (no fields), `wait` (`code`, the 19-bit implementation-dependent
    field).
- Prefetch `pref` (`rs hint imm`): a no-op.
- Coprocessor-1 (FPU) — opcodes `0x11` (COP1), `0x13` (COP1X) and the
  load/store opcodes; `fmt` is `S` = 0x10, `D` = 0x11, `W` = 0x14. A double
  in `$fN` occupies the register pair `fpRegs[N]` (low word) / `fpRegs[N+1]`
  (high word): the 32-bit FPU register model, `Status.FR = 0`. `fd`/`fs`/
  `ft`/`fr` name the low register of a pair. An odd register number for a
  double is UNPREDICTABLE in the architecture; the model uses the pair
  `(N, N+1 mod 32)` regardless (pin).
  - moves: `mfc1 mtc1 mfhc1 mthc1` (`rt fs`), `cfc1 ctc1` (`rt fs`, control
    registers);
  - loads/stores: `lwc1 swc1 ldc1 sdc1` (`rs ft imm`), indexed `lwxc1 ldxc1`
    (`fd index base`), `swxc1 sdxc1` (`fs index base`), `prefx`
    (`hint index base`);
  - arithmetic: `add sub mul div` (`fd fs ft`), `sqrt abs neg recip rsqrt`
    (`fd fs`), `madd msub nmadd nmsub` (`fd fr fs ft`), each `.S`/`.D`;
  - conversions (`fd fs`): `cvt.s.w cvt.d.w cvt.s.d cvt.d.s`,
    `cvt.w round.w trunc.w ceil.w floor.w` from `.S`/`.D`;
  - compare: `cCondS`/`cCondD` (`cond cc fs ft`) — one constructor per format
    for all sixteen `C.cond.fmt` predicates (`cond` = bits 3..0) and all
    eight condition codes (`cc` = bits 10..8);
  - non-arithmetic moves: `mov` (`fd fs`), `movf movt` (`fd fs cc`),
    `movn movz` (`fd fs rt`), each `.S`/`.D`; and the GPR `movf`/`movt`
    (`rs cc rd`, SPECIAL `MOVCI`);
  - branches `bc1f bc1t bc1fl bc1tl` (`cc imm`).
  Not modeled (they do not decode): the L (64-bit fixed point) format,
  `luxc1`/`suxc1` and paired-single — all UNPREDICTABLE with `FR = 0`
  (see `docs/spec/SPEC-NOTES.md`).
-/

/-- The modeled MIPS32 Release 2 machine-instruction set (one constructor per
instruction; the field-shape summary in the module docstring groups them).
Each constructor's fields are the **raw** bit-field
values extracted from the 32-bit encoding — see the module docstring for
which fields each variant carries and INSTRUCTION-REF for the exact bit
layout and semantics. -/
inductive Instruction where
  -- R-type reg/reg/reg
  /-- `$rd = $rs + $rt`, signed; traps on overflow (opcode 0, funct 0x20). -/
  | add  (rs rt rd : W32)
  /-- `$rd = $rs + $rt`, wraps (opcode 0, funct 0x21). -/
  | addu (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, signed; traps on overflow (opcode 0, funct 0x22). -/
  | sub  (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, wraps (opcode 0, funct 0x23). -/
  | subu (rs rt rd : W32)
  /-- `$rd = $rs & $rt` (opcode 0, funct 0x24). -/
  | and  (rs rt rd : W32)
  /-- `$rd = $rs | $rt` (opcode 0, funct 0x25). -/
  | or   (rs rt rd : W32)
  /-- `$rd = $rs ^ $rt` (opcode 0, funct 0x26). -/
  | xor  (rs rt rd : W32)
  /-- `$rd = ~($rs | $rt)` (opcode 0, funct 0x27). -/
  | nor  (rs rt rd : W32)
  /-- `$rd = ($rs < $rt) ? 1 : 0`, signed (opcode 0, funct 0x2a). -/
  | slt  (rs rt rd : W32)
  /-- `$rd = ($rs <u $rt) ? 1 : 0`, unsigned (opcode 0, funct 0x2b). -/
  | sltu (rs rt rd : W32)
  /-- `$rd = $rs` if `$rt != 0`; `$rd` unchanged otherwise (a real conditional
  no-op, not "write 0") (opcode 0, funct 0x0b). MIPS32r2. -/
  | movn (rs rt rd : W32)
  /-- `$rd = $rs` if `$rt == 0`; `$rd` unchanged otherwise (opcode 0,
  funct 0x0a). MIPS32r2. -/
  | movz (rs rt rd : W32)
  -- R-type shift (rs unused)
  /-- `$rd = $rt << shamt`, logical (opcode 0, funct 0x00). -/
  | sll  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, logical/zero-fill (opcode 0, funct 0x02). -/
  | srl  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, arithmetic/sign-fill (opcode 0, funct 0x03). -/
  | sra  (rd rt shamt : W32)
  -- R-type variable shift (opcode 0; shamt field unused/fixed 0). MIPS32
  -- v1.x addition: compilers emit these (not `sll`/`srl`/`sra`) whenever
  -- the shift amount is a runtime value rather than a compile-time
  -- constant (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.4).
  /-- `$rd = $rt << ($rs & 0x1f)`, logical, shift amount from a register's
  low 5 bits (opcode 0, funct 0x04). MIPS32. -/
  | sllv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, logical/zero-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x06). MIPS32. -/
  | srlv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, arithmetic/sign-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x07). MIPS32. -/
  | srav (rd rt rs : W32)
  -- R-type rotate (MIPS32r2; docs/spec/MIPS-COVERAGE-GAPS.md §3.4). Real
  -- MIPS32r2 overloads `srl`'s opcode-0/funct-0x02 encoding: the `rs` field
  -- (normally unused/fixed 0 for the plain shift-by-constant format) is set
  -- to 0x01 to select rotate instead of shift. Likewise `srlv`'s
  -- opcode-0/funct-0x06 encoding is overloaded via the (normally
  -- unused/fixed 0) `shamt` field set to 0x01. These are new decode/encode
  -- branches alongside the existing `srl`/`srlv` ones, not replacements.
  /-- `$rd = $rt` rotated right by the constant `sa` (0-31) bits -- bits
  shifted off the bottom wrap around to the top, unlike `srl`'s zero-fill
  (opcode 0, funct 0x02, `rs` field = 0x01). MIPS32r2. -/
  | rotr (rd rt sa : W32)
  /-- `$rd = $rt` rotated right by `$rs & 0x1f` bits, rotate amount from a
  register's low 5 bits (opcode 0, funct 0x06, `shamt` field = 0x01).
  MIPS32r2. -/
  | rotrv (rd rt rs : W32)
  -- R-type mult/div (rd, shamt unused)
  /-- `{hi,lo} = $rs * $rt`, signed 64-bit (opcode 0, funct 0x18). -/
  | mult   (rs rt : W32)
  /-- `{hi,lo} = $rs * $rt`, unsigned 64-bit (opcode 0, funct 0x19). -/
  | multu  (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, signed (opcode 0, funct 0x1a). -/
  | div    (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, unsigned (opcode 0, funct 0x1b). -/
  | divu   (rs rt : W32)
  -- R-type move (rs, rt, shamt unused)
  /-- `$rd = lo` (opcode 0, funct 0x12). -/
  | mflo (rd : W32)
  /-- `$rd = hi` (opcode 0, funct 0x10). -/
  | mfhi (rd : W32)
  -- R-type move, write direction (rt, rd/shamt unused): the write-direction
  -- counterparts to `mfhi`/`mflo` above (opcode 0, funct 0x11/0x13 — the
  -- next funct values immediately after `mfhi`'s 0x10/`mflo`'s 0x12, the
  -- same adjacency pattern as `syscall` 0x0c/`break` 0x0d). Real MIPS32
  -- (MD00086 Rev 2.50 §3.2, Table 3-7); needed for OS context switching and
  -- setjmp/longjmp to save/restore `hi`/`lo` (see
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
  /-- `hi = $rs` (opcode 0, funct 0x11). MIPS32. -/
  | mthi (rs : W32)
  /-- `lo = $rs` (opcode 0, funct 0x13). MIPS32. -/
  | mtlo (rs : W32)
  -- R-type jump register (rt, rd/shamt unused as noted per-constructor). Real
  -- MIPS32 register-indirect jump/call family — shares opcode 0 (SPECIAL)
  -- with the R-type arithmetic instructions above, distinguished by funct.
  /-- `PC = $rs`, after the usual one-instruction delay slot (opcode 0,
  funct 0x08). Real MIPS32 register-indirect jump (MD00086 §3.2); `rt`/`rd`/
  `shamt` are 0 in the real encoding and carry no information. The canonical
  function-return idiom is `jr $ra`. -/
  | jr (rs : W32)
  /-- `$rd = PC_next + 4` (the address of the instruction *after* the delay
  slot — same `pc + 8` link-value convention as `jal`); `PC = $rs`, after
  the usual one-instruction delay slot (opcode 0, funct 0x09). Real MIPS32
  register-indirect call (MD00086 §3.2), used for indirect procedure calls
  and function pointers (e.g. `jalr $t9`); `rt`/`shamt` are 0 in the real
  encoding and carry no information. -/
  | jalr (rs rd : W32)
  -- R-type SPECIAL2 bit-count (MIPS32). The real 32-bit encoding's `rt` field
  -- (bits 20..16) duplicates `rd` (bits 15..11) "because both fields hold the
  -- same register number" per the ISA; hardware does not read `rt` for these
  -- two instructions, so it carries no independent information and is not
  -- modeled as a separate field here (`encode` reconstructs the duplicate).
  /-- `$rd = ` the number of leading one bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-ones) (SPECIAL2 opcode 0x1c, funct 0x21). MIPS32. -/
  | clo (rs rd : W32)
  /-- `$rd = ` the number of leading zero bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-zero) (SPECIAL2 opcode 0x1c, funct 0x20). MIPS32. -/
  | clz (rs rd : W32)
  -- R-type GPR multiply, SPECIAL2 (MIPS32). Unlike `clo`/`clz`, this is a
  -- plain `rs rt rd` shape with no duplicated-field quirk.
  /-- `$rd = ` low 32 bits of `$rs * $rt`, signed (SPECIAL2 opcode 0x1c,
  funct 0x02). `hi`/`lo` are left **unchanged** by this dialect (real
  MIPS32 hardware leaves them architecturally unpredictable after `mul`;
  see `docs/spec/INSTRUCTION-REF.md` for the documented dialect choice).
  MIPS32. -/
  | mul (rs rt rd : W32)
  -- R-type multiply-accumulate, SPECIAL2 (MIPS32). Same `rs rt` field shape
  -- as `mult`/`multu` (`rd`/`shamt` unused) -- these accumulate into the
  -- *existing* `hi`/`lo` 64-bit pair instead of overwriting it, the core
  -- loop instruction in DSP filters, vector dot-products, and numerical
  -- libraries (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5). Ground truth:
  -- MD00086 Rev 2.50 §3.2, Table 3-1.
  /-- `{hi,lo} += $rs * $rt`, signed 64-bit, wrapping on overflow like
  `mult` (SPECIAL2 opcode 0x1c, funct 0x00). MIPS32. -/
  | madd  (rs rt : W32)
  /-- `{hi,lo} += $rs * $rt`, unsigned 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x01). MIPS32. -/
  | maddu (rs rt : W32)
  /-- `{hi,lo} -= $rs * $rt`, signed 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x04). MIPS32. -/
  | msub  (rs rt : W32)
  /-- `{hi,lo} -= $rs * $rt`, unsigned 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x05). MIPS32. -/
  | msubu (rs rt : W32)
  -- R-type SPECIAL3 BSHFL sign-extend (MIPS32r2). `rs` is unused/fixed 0;
  -- `funct` is 0x20 for the whole BSHFL sub-op family, and the shamt-position
  -- 5-bit sub-field (not a real shift amount here) selects which one.
  /-- `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x10). MIPS32r2. -/
  | seb (rd rt : W32)
  /-- `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x18). MIPS32r2. -/
  | seh (rd rt : W32)
  /-- "Word Swap Bytes Within Halfwords": swaps the byte order *within* each
  16-bit half of `$rt` independently (byte 0 <-> 1, byte 2 <-> 3), leaving
  the two halfwords in their original word positions -- **not** a full
  32-bit byte-reverse (that needs `wsbh` followed by `rotr` by 16)
  (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x02 -- same BSHFL funct
  family as `seb`/`seh`, distinguished by the sub-field like they are).
  MIPS32r2. -/
  | wsbh (rd rt : W32)
  -- R-type SPECIAL3 bitfield extract/insert (MIPS32r2;
  -- docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). Both `pos` and `size` are
  -- small compile-time constants (0-31) encoded directly in the
  -- instruction word, not register values. Real constraint `pos + size <=
  -- 32` is architecturally UNPREDICTABLE if violated; this model makes no
  -- special case for it (SPEC-NOTES precedent: just compute what the
  -- bit masking implies). The raw encoding packs `pos` into the `shamt`
  -- field (bits 10..6) for both instructions, but the `rd`-position field
  -- (bits 15..11) differs: for `ext` it holds `size - 1` ("msbd"); for
  -- `ins` it holds `pos + size - 1` ("msb") -- these are genuinely
  -- different fields in the real MIPS32 ISA (MD00086 section 3.2), not a
  -- typo. `decode`/`encode` below do the +-1 arithmetic so `Step.lean`
  -- only ever sees the semantic `pos`/`size` pair.
  /-- `$rt = zero-extend($rs[pos+size-1 .. pos])`, extracting a `size`-bit
  field starting at bit `pos` (SPECIAL3 opcode 0x1f, funct 0x00). MIPS32r2. -/
  | ext (rt rs pos size : W32)
  /-- Inserts the low `size` bits of `$rs` into `$rt` starting at bit `pos`;
  bits of `$rt` outside `[pos+size-1 .. pos]` are left unchanged (SPECIAL3
  opcode 0x1f, funct 0x04). MIPS32r2. -/
  | ins (rt rs pos size : W32)
  -- SPECIAL3 RDHWR (MIPS32 Release 2): read a hardware register (`HWREna`-gated).
  /-- Read Hardware Register: `$rt = HWR[rd]` (SPECIAL3 opcode 0x1f, funct 0x3b, `rs` = 0, bits
  10..6 = 0; MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334; "MIPS32 Release 2"). The model implements
  `rd` = 0 `CPUNum`, 1 `SYNCI_Step`, 2 `CC` (= `Count`), 3 `CCRes`; access needs Coprocessor 0 to be
  enabled or the `HWREna` bit `rd` set, otherwise (and for every other `rd`) Reserved Instruction
  (`Step.lean`). The Release 6 `sel` field (bits 8..6) does not exist before Release 6 (Rev 2.50
  RDHWR p.229: bits 10..6 are `0`), so a nonzero value does not decode. -/
  | rdhwr (rt rd : W32)
  -- I-type arith/logic
  /-- `$rt = $rs + sext16(imm)`, traps on overflow (opcode 0x08). -/
  | addi  (rs rt imm : W32)
  /-- `$rt = $rs + sext16(imm)`, wraps (opcode 0x09). -/
  | addiu (rs rt imm : W32)
  /-- `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed (opcode 0x0a). -/
  | slti  (rs rt imm : W32)
  /-- `$rt = ($rs <u sext16(imm)) ? 1 : 0` (opcode 0x0b). -/
  | sltiu (rs rt imm : W32)
  /-- `$rt = $rs & zext16(imm)` (opcode 0x0c). -/
  | andi  (rs rt imm : W32)
  /-- `$rt = $rs | zext16(imm)` (opcode 0x0d). -/
  | ori   (rs rt imm : W32)
  /-- `$rt = $rs ^ zext16(imm)` (opcode 0x0e). -/
  | xori  (rs rt imm : W32)
  -- I-type lui (rs unused/fixed 0)
  /-- `$rt = imm << 16` (opcode 0x0f). -/
  | lui   (rt imm : W32)
  -- I-type load/store: rs = base, rt = dest/src, imm = raw offset field
  /-- `$rt = MEM32[$rs + offset]`, word-aligned (opcode 0x23). -/
  | lw  (rs rt imm : W32)
  /-- `MEM32[$rs + offset] = $rt`, word-aligned (opcode 0x2b). -/
  | sw  (rs rt imm : W32)
  /-- `$rt = sext8(MEM8[$rs + offset])` (opcode 0x20). -/
  | lb  (rs rt imm : W32)
  /-- `$rt = zext8(MEM8[$rs + offset])` (opcode 0x24). -/
  | lbu (rs rt imm : W32)
  /-- `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x21). -/
  | lh  (rs rt imm : W32)
  /-- `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x25). -/
  | lhu (rs rt imm : W32)
  /-- `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned (opcode 0x29). -/
  | sh  (rs rt imm : W32)
  /-- `MEM8[$rs + offset] = $rt[7:0]`, no alignment requirement (opcode 0x28;
  MD00086 Rev 2.50 "SB"). -/
  | sb  (rs rt imm : W32)
  /-- `$rt = MEM32[$rs + offset]`, word-aligned, and sets `State.llBit`
  (real MIPS32 "Load Linked Word", opcode 0x30; MD00086 Rev 2.50 §3.2,
  Table 3-4). Identical addressing/alignment to `lw`; see
  `docs/spec/INSTRUCTION-REF.md` for the paired `sc` semantics and this
  model's single-hart `llBit` simplification. -/
  | ll  (rs rt imm : W32)
  /-- Conditionally `MEM32[$rs + offset] = $rt`, word-aligned, based on
  `State.llBit`: if set, performs the store and writes `1` to `$rt`;
  otherwise the store does not happen and `0` is written to `$rt`. Either
  way, clears `llBit` (real MIPS32 "Store Conditional Word", opcode 0x38;
  MD00086 Rev 2.50 §3.2, Table 3-4). Identical addressing/alignment to
  `sw`. -/
  | sc  (rs rt imm : W32)
  -- I-type unaligned load/store (classic MIPS32; removed in MIPS32r6). Same
  -- `rs rt imm` field shape as `lw`/`sw`; see `docs/spec/INSTRUCTION-REF.md`'s
  -- dedicated section for the exact big-endian byte-merge semantics.
  /-- Load Word Left (opcode 0x22; MD00086 Rev 2.50 §3.2, Table 3-4, p. 25,
  entry 174). `addr = $rs + sext16(offset)` (no alignment check). Loads the
  bytes from `addr` up to the next word boundary (inclusive of `addr`) into
  the most-significant bytes of `$rt`; `$rt`'s remaining (less-significant)
  bytes are left unchanged. -/
  | lwl (rs rt imm : W32)
  /-- Load Word Right (opcode 0x26; MD00086 Rev 2.50 §3.2, Table 3-4, p. 25,
  entry 177). Same `addr` as `lwl`. Loads the bytes from the start of the
  word containing `addr` up to and including `addr` into the
  least-significant bytes of `$rt`; `$rt`'s remaining (more-significant)
  bytes are left unchanged. Paired with `lwl` (opposite offsets) to load an
  arbitrary unaligned word. -/
  | lwr (rs rt imm : W32)
  /-- Store Word Left (opcode 0x2a; MD00086 Rev 2.50 §3.2, Table 3-4, p. 26,
  entry 282). Same `addr` as `lwl`. Stores `$rt`'s most-significant bytes
  into memory from `addr` up to the next word boundary (inclusive of
  `addr`). -/
  | swl (rs rt imm : W32)
  /-- Store Word Right (opcode 0x2e; MD00086 Rev 2.50 §3.2, Table 3-4, p. 26,
  entry 285). Same `addr` as `lwl`. Stores `$rt`'s least-significant bytes
  into memory from the start of the word containing `addr` up to and
  including `addr`. Paired with `swl` to store an arbitrary unaligned
  word. -/
  | swr (rs rt imm : W32)
  -- I-type branch reg/reg
  /-- `if $rs == $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x04). -/
  | beq (rs rt imm : W32)
  /-- `if $rs != $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x05). -/
  | bne (rs rt imm : W32)
  -- I-type branch reg-only (rt unused/fixed 0)
  /-- `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x06). -/
  | blez (rs imm : W32)
  /-- `if $rs > 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x07). -/
  | bgtz (rs imm : W32)
  -- I-type REGIMM zero-comparison branches (MIPS32 ISA; opcode 0x01). All
  -- four share this one opcode; the `rt` field (not a separate opcode)
  -- selects which instruction it is (ground truth: MD00086 Rev 2.50 §3.2,
  -- Table 3-2, p. 25; see docs/spec/INSTRUCTION-REF.md for the full
  -- citation). Same `rs, offset` field shape as `blez`/`bgtz`.
  /-- `if $rs < 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x00 `BLTZ`). -/
  | bltz (rs imm : W32)
  /-- `if $rs >= 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x01 `BGEZ`). -/
  | bgez (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally, **then** `if $rs < 0 then
  PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x10
  `BLTZAL`). Real MIPS32: the link into `$ra` always happens (it is not
  conditional on the branch being taken), same convention as `jal`'s link —
  see docs/spec/INSTRUCTION-REF.md for the citation. The real ISA
  pseudocode links `$ra` one cycle before testing `$rs`, so `rs = $ra` (31)
  is architecturally UNPREDICTABLE (the test could observe either the old
  or the freshly-linked value); `Step.lean` resolves this by testing the
  pre-link value of `$rs`, a documented, defensible choice for an
  explicitly-unspecified case rather than an oversight. -/
  | bltzal (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally, **then** `if $rs >= 0 then
  PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x11
  `BGEZAL`). Same unconditional-link convention and `rs = $ra`
  UNPREDICTABLE-case resolution as `bltzal`. -/
  | bgezal (rs imm : W32)
  -- I-type "branch likely" family (real MIPS32 ISA; deprecated in MIPS32,
  -- removed in Release 6 -- MD00086 Rev 2.50 section 3.2, Table 3-10, p. 28;
  -- see docs/spec/MIPS-COVERAGE-GAPS.md section 3.3). Field shapes are
  -- identical to their non-likely counterparts directly above (beq/bne:
  -- rs rt imm; blez/bgtz/bltz/bgez/bltzal/bgezal: rs imm). The one
  -- architectural difference -- and the reason these are not just aliases
  -- of the plain branches -- is the delay slot: a not-taken branch-likely
  -- instruction nullifies (squashes) its own delay-slot instruction
  -- instead of executing it. `Instruction.lean`/`Asm.lean` treat these as
  -- ordinary field-shape-only mnemonics; the squash mechanism itself lives
  -- entirely in `Step.lean` (`State.squashNext`), since decode/encode have
  -- no notion of "what happens next". `beql`/`bnel`: opcode 0x14/0x15.
  -- `blezl`/`bgtzl`: opcode 0x16/0x17. `bltzl`/`bgezl`/`bltzall`/`bgezall`:
  -- REGIMM (opcode 0x01), rt field 0x02/0x03/0x12/0x13.
  /-- `if $rs == $rt then PC = PC_next + (sext16(imm) << 2); else squash the
  delay-slot instruction` (opcode 0x14, `BEQL`). See `Step.lean`'s
  `.beql` case and `State.squashNext`'s docstring for the squash mechanism. -/
  | beql (rs rt imm : W32)
  /-- `if $rs != $rt then PC = PC_next + (sext16(imm) << 2); else squash`
  (opcode 0x15, `BNEL`). Same shape/mechanism as `beql`. -/
  | bnel (rs rt imm : W32)
  /-- `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2); else squash`,
  signed (opcode 0x16, `BLEZL`; `rt` field fixed 0). Same mechanism as
  `beql`. -/
  | blezl (rs imm : W32)
  /-- `if $rs > 0 then PC = PC_next + (sext16(imm) << 2); else squash`,
  signed (opcode 0x17, `BGTZL`; `rt` field fixed 0). Same mechanism as
  `beql`. -/
  | bgtzl (rs imm : W32)
  /-- `if $rs < 0 then PC = PC_next + (sext16(imm) << 2); else squash`,
  signed (opcode 0x01, `rt` field = 0x02 `BLTZL`). Same mechanism as
  `beql`. -/
  | bltzl (rs imm : W32)
  /-- `if $rs >= 0 then PC = PC_next + (sext16(imm) << 2); else squash`,
  signed (opcode 0x01, `rt` field = 0x03 `BGEZL`). Same mechanism as
  `beql`. -/
  | bgezl (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally (same unconditional-link
  convention as `bltzal`, including on the not-taken/squashed path),
  **then** `if $rs < 0 then PC = PC_next + (sext16(imm) << 2); else squash`
  (opcode 0x01, `rt` field = 0x12 `BLTZALL`). -/
  | bltzall (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally, **then** `if $rs >= 0 then
  PC = PC_next + (sext16(imm) << 2); else squash` (opcode 0x01, `rt` field
  = 0x13 `BGEZALL`). Same unconditional-link convention as `bltzall`. -/
  | bgezall (rs imm : W32)
  -- I-type REGIMM trap-immediate family (real MIPS32 ISA; opcode 0x01,
  -- same opcode as the zero-comparison branches above, selected by the
  -- same `rt`-field multiplexing). Not part of the original v1 instruction
  -- set, added on top as the sign-extended-16-bit-immediate counterpart of
  -- the `teq tne tlt tge tltu tgeu` register-register trap family below
  -- (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8); funct/rt values are cited
  -- from the real MIPS32 ISA (MD00086 Rev 2.50 §3.2, Table 3-2), not MARS.
  /-- `if $rs == sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0c `TEQI`). -/
  | teqi (rs imm : W32)
  /-- `if $rs != sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0e `TNEI`). -/
  | tnei (rs imm : W32)
  /-- `if $rs >= sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x08 `TGEI`). -/
  | tgei (rs imm : W32)
  /-- `if $rs >=u sext16(imm) then trap`: the immediate is sign-extended to
  32 bits first, then the comparison is unsigned on the resulting bit
  patterns — same "sign-extend, then compare unsigned" convention as
  `sltiu` (opcode 0x01, `rt` field = 0x09 `TGEIU`). -/
  | tgeiu (rs imm : W32)
  /-- `if $rs < sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0a `TLTI`). -/
  | tlti (rs imm : W32)
  /-- `if $rs <u sext16(imm) then trap`: same sign-extend-then-unsigned-compare
  convention as `tgeiu`/`sltiu` (opcode 0x01, `rt` field = 0x0b `TLTIU`). -/
  | tltiu (rs imm : W32)
  -- Instruction-cache synchronize hint (real MIPS32 ISA, MIPS32r2; see
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7). Shares REGIMM's opcode 0x01
  -- with the branch/trap-immediate families above, selected the same way
  -- (by the `rt` field, here fixed to `0x1f`), but its remaining operands
  -- (`rs`, `imm`) are an address computation like `lw`/`sw`/`blez`, not a
  -- branch target or trap comparand.
  /-- Hint to flush the instruction cache at `$rs + sext16(offset)`, for
  self-modifying code / JIT compilers (opcode 0x01 REGIMM, `rt` field =
  `0x1f` `SYNCI`). This simulator has no instruction-cache model, so
  `Step.lean` computes the address (exactly like `lw`/`sw`) but never uses
  it for anything -- a documented no-op, not a silently-dropped cache
  effect. -/
  | synci (rs imm : W32)
  -- J-type
  /-- `PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x02). -/
  | j   (target : W32)
  /-- `$ra = PC_next; PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x03). -/
  | jal (target : W32)
  -- syscall (no fields; the syscall number lives in $v0 at execution time)
  /-- System call (opcode 0, funct 0x0c); `code` = bits 25..6, ignored by
  execution. The environment-call number is `$v0` (services 1/4/10/11). -/
  | syscall (code : W32)
  -- R-type trap-on-condition (rd, shamt unused) — real MIPS32 SPECIAL-opcode
  -- trap family. Not modeled realistically by MARS (see
  -- docs/spec/INSTRUCTION-REF.md); funct values below are the standard
  -- MIPS32 ISA encoding, cited from the real architecture, not MARS.
  /-- `if $rs == $rt then trap` (opcode 0, funct 0x34). `code` = bits 15..6, ignored by execution. -/
  | teq (rs rt code : W32)
  /-- `if $rs != $rt then trap` (opcode 0, funct 0x36). `code` = bits 15..6, ignored by execution. -/
  | tne (rs rt code : W32)
  /-- `if $rs < $rt then trap`, signed (opcode 0, funct 0x32). `code` = bits 15..6, ignored by execution. -/
  | tlt (rs rt code : W32)
  /-- `if $rs >= $rt then trap`, signed (opcode 0, funct 0x30). `code` = bits 15..6, ignored by execution. -/
  | tge (rs rt code : W32)
  /-- `if $rs <u $rt then trap`, unsigned (opcode 0, funct 0x33). `code` = bits 15..6, ignored by execution. -/
  | tltu (rs rt code : W32)
  /-- `if $rs >=u $rt then trap`, unsigned (opcode 0, funct 0x31). `code` = bits 15..6, ignored by execution. -/
  | tgeu (rs rt code : W32)
  /-- Unconditional Breakpoint exception (opcode 0, funct 0x0d); `code` =
  bits 25..6, "available for use as software parameters" (MD00086 Vol II-A
  Rev 6.06, BREAK, p.109). -/
  | break (code : W32)
  /-- Memory-ordering barrier (opcode 0, funct 0x0f); `stype` = bits 10..6.
  A no-op in this single-hart model, for every `stype`. -/
  | sync (stype : W32)
  /-- Prefetch (opcode 0x33): `hint` = bits 20..16. "Any action, including
  doing nothing, is permitted"; "PREF does not cause addressing-related
  exceptions" (MD00086 Vol II-A Rev 6.06, PREF, p.321). A no-op here. -/
  | pref (rs hint imm : W32)
  -- Coprocessor 0 (opcode 0x10).
  /-- `$rt = ` CP0 register `(rd, sel)` (`rs`-field = `MF` = 0x00). `decode`
  produces this only for a modeled pair (`isModeledCp0Reg`). -/
  | mfc0 (rt rd sel : W32)
  /-- CP0 register `(rd, sel) := $rt` (`rs`-field = `MT` = 0x04), through the
  register's write mask (`Step.lean`). Same scoping as `mfc0`. -/
  | mtc0 (rt rd sel : W32)
  /-- Disable interrupts: `$rt = Status; Status.IE = 0` (`rs`-field = `MFMC0`
  = 0x0b, `rd` = 12, `sc` = bit 5 = 0; MD00086 Vol II-A Rev 6.06, DI, p.164). -/
  | di (rt : W32)
  /-- Enable interrupts: `$rt = Status; Status.IE = 1` (as `di`, `sc` = 1;
  MD00086 Vol II-A Rev 6.06, EI, p.176). -/
  | ei (rt : W32)
  /-- Exception return: `PC := cp0Epc`, `Status.EXL := 0` (opcode 0x10 COP0,
  `rs`-field = `CO` = 0x10, `funct` = 0x18). No operands. Real MIPS32:
  **not** a delay-slotted instruction — it takes effect immediately, an
  architectural exception to the general branch/jump delay-slot rule (see
  `Step.lean`'s execution semantics and `docs/spec/INSTRUCTION-REF.md`). -/
  | eret
  /-- Enter standby mode (opcode 0x10 COP0, bit 25 = `CO` = 1, `funct` =
  0x20); `code` = the 19-bit implementation-dependent field, bits 24..6.
  This model has no interrupt, so it is a no-op that falls through. -/
  | wait (code : W32)
  -- Coprocessor 1 (FPU). Citations: MD00086 Vol II-A Rev 6.06, by
  -- instruction name; semantics in `Step.lean` / `FpOps.lean`.
  /-- `$rt = FPR[fs]` raw low word (COP1, `rs` = `MF` = 0x00). -/
  | mfc1 (rt fs : W32)
  /-- `FPR[fs] = $rt` raw word (COP1, `rs` = `MT` = 0x04). -/
  | mtc1 (rt fs : W32)
  /-- `$rt = ` high word of the double in `fs`, i.e. `FPR[fs+1]` (COP1, `rs` =
  `MFH` = 0x03; Release 2). -/
  | mfhc1 (rt fs : W32)
  /-- High word of the double in `fs` (`FPR[fs+1]`) `= $rt` (COP1, `rs` =
  `MTH` = 0x07; Release 2). -/
  | mthc1 (rt fs : W32)
  /-- `$rt = FP_Control[fs]` (COP1, `rs` = `CF` = 0x02): FIR 0, FCCR 25,
  FEXR 26, FENR 28, FCSR 31. -/
  | cfc1 (rt fs : W32)
  /-- `FP_Control[fs] = $rt` (COP1, `rs` = `CT` = 0x06), then
  CheckFPException. -/
  | ctc1 (rt fs : W32)
  /-- `FPR[ft] = MEM32[$rs + sext(imm)]` (opcode 0x31). -/
  | lwc1 (rs ft imm : W32)
  /-- `MEM32[$rs + sext(imm)] = FPR[ft]` (opcode 0x39). -/
  | swc1 (rs ft imm : W32)
  /-- `{FPR[ft+1],FPR[ft]} = MEM64[$rs + sext(imm)]`, doubleword-aligned
  (opcode 0x35). -/
  | ldc1 (rs ft imm : W32)
  /-- `MEM64[$rs + sext(imm)] = {FPR[ft+1],FPR[ft]}`, doubleword-aligned
  (opcode 0x3d). -/
  | sdc1 (rs ft imm : W32)
  /-- `FPR[fd] = MEM32[$base + $index]` (COP1X, funct 0x00; Release 2). -/
  | lwxc1 (fd index base : W32)
  /-- `{FPR[fd+1],FPR[fd]} = MEM64[$base + $index]` (COP1X, funct 0x01). -/
  | ldxc1 (fd index base : W32)
  /-- `MEM32[$base + $index] = FPR[fs]` (COP1X, funct 0x08). -/
  | swxc1 (fs index base : W32)
  /-- `MEM64[$base + $index] = {FPR[fs+1],FPR[fs]}` (COP1X, funct 0x09). -/
  | sdxc1 (fs index base : W32)
  /-- Prefetch indexed (COP1X, funct 0x0f): a no-op (but, being COP1X, it
  needs `Status.CU1`). -/
  | prefx (hint index base : W32)
  -- Arithmetic, single (fmt = S = 0x10).
  /-- `fd = fs + ft` (funct 0x00). -/
  | addS (fd fs ft : W32)
  /-- `fd = fs − ft` (funct 0x01). -/
  | subS (fd fs ft : W32)
  /-- `fd = fs × ft` (funct 0x02). -/
  | mulS (fd fs ft : W32)
  /-- `fd = fs / ft` (funct 0x03). -/
  | divS (fd fs ft : W32)
  /-- `fd = sqrt fs` (funct 0x04). -/
  | sqrtS (fd fs : W32)
  /-- `fd = |fs|`, arithmetic (funct 0x05). -/
  | absS (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movS (fd fs : W32)
  /-- `fd = −fs`, arithmetic (funct 0x07). -/
  | negS (fd fs : W32)
  /-- `fd = 1.0 / fs` (funct 0x15; Release 2). -/
  | recipS (fd fs : W32)
  /-- `fd = 1.0 / sqrt fs` (funct 0x16; Release 2). -/
  | rsqrtS (fd fs : W32)
  /-- Single → word, round to nearest even (funct 0x0c). -/
  | roundWS (fd fs : W32)
  /-- Single → word, round toward zero (funct 0x0d). -/
  | truncWS (fd fs : W32)
  /-- Single → word, round toward +∞ (funct 0x0e). -/
  | ceilWS (fd fs : W32)
  /-- Single → word, round toward −∞ (funct 0x0f). -/
  | floorWS (fd fs : W32)
  /-- Single → word, rounding per FCSR.RM (funct 0x24). -/
  | cvtWS (fd fs : W32)
  /-- Single → double (fmt = S, funct 0x21). -/
  | cvtDS (fd fs : W32)
  /-- Word → single, rounding per FCSR.RM (fmt = W = 0x14, funct 0x20). -/
  | cvtSW (fd fs : W32)
  /-- Word → double, exact (fmt = W, funct 0x21). -/
  | cvtDW (fd fs : W32)
  -- Arithmetic, double (fmt = D = 0x11).
  /-- `fd = fs + ft` (funct 0x00). -/
  | addD (fd fs ft : W32)
  /-- `fd = fs − ft` (funct 0x01). -/
  | subD (fd fs ft : W32)
  /-- `fd = fs × ft` (funct 0x02). -/
  | mulD (fd fs ft : W32)
  /-- `fd = fs / ft` (funct 0x03). -/
  | divD (fd fs ft : W32)
  /-- `fd = sqrt fs` (funct 0x04). -/
  | sqrtD (fd fs : W32)
  /-- `fd = |fs|`, arithmetic (funct 0x05). -/
  | absD (fd fs : W32)
  /-- `fd = fs`, non-arithmetic (funct 0x06). -/
  | movD (fd fs : W32)
  /-- `fd = −fs`, arithmetic (funct 0x07). -/
  | negD (fd fs : W32)
  /-- `fd = 1.0 / fs` (funct 0x15; Release 2). -/
  | recipD (fd fs : W32)
  /-- `fd = 1.0 / sqrt fs` (funct 0x16; Release 2). -/
  | rsqrtD (fd fs : W32)
  /-- Double → word, round to nearest even (funct 0x0c). -/
  | roundWD (fd fs : W32)
  /-- Double → word, round toward zero (funct 0x0d). -/
  | truncWD (fd fs : W32)
  /-- Double → word, round toward +∞ (funct 0x0e). -/
  | ceilWD (fd fs : W32)
  /-- Double → word, round toward −∞ (funct 0x0f). -/
  | floorWD (fd fs : W32)
  /-- Double → word, rounding per FCSR.RM (funct 0x24). -/
  | cvtWD (fd fs : W32)
  /-- Double → single, rounding per FCSR.RM (fmt = D, funct 0x20). -/
  | cvtSD (fd fs : W32)
  -- Compare: funct = 0x30 | cond; bits 10..8 = cc; bits 7..6 = 0.
  /-- `C.cond.S`: `FCC[cc] = fs compare_cond ft` (singles). `cond` (4 bits):
  0 F, 1 UN, 2 EQ, 3 UEQ, 4 OLT, 5 ULT, 6 OLE, 7 ULE, 8 SF, 9 NGLE, 10 SEQ,
  11 NGL, 12 LT, 13 NGE, 14 LE, 15 NGT. -/
  | cCondS (cond cc fs ft : W32)
  /-- `C.cond.D`: as `cCondS`, on doubles. -/
  | cCondD (cond cc fs ft : W32)
  -- Conditional moves (non-arithmetic).
  /-- `if FCC[cc] = 0 then fd = fs`, single (fmt S, funct 0x11, `tf` = 0). -/
  | movfS (fd fs cc : W32)
  /-- `if FCC[cc] = 1 then fd = fs`, single (funct 0x11, `tf` = 1). -/
  | movtS (fd fs cc : W32)
  /-- `if FCC[cc] = 0 then fd = fs`, double. -/
  | movfD (fd fs cc : W32)
  /-- `if FCC[cc] = 1 then fd = fs`, double. -/
  | movtD (fd fs cc : W32)
  /-- `if $rt ≠ 0 then fd = fs`, single (funct 0x13). -/
  | movnS (fd fs rt : W32)
  /-- `if $rt = 0 then fd = fs`, single (funct 0x12). -/
  | movzS (fd fs rt : W32)
  /-- `if $rt ≠ 0 then fd = fs`, double. -/
  | movnD (fd fs rt : W32)
  /-- `if $rt = 0 then fd = fs`, double. -/
  | movzD (fd fs rt : W32)
  /-- `if FCC[cc] = 0 then $rd = $rs` (SPECIAL funct 0x01 `MOVCI`, `tf` = 0).
  Needs `Status.CU1`. -/
  | movf (rs cc rd : W32)
  /-- `if FCC[cc] = 1 then $rd = $rs` (SPECIAL `MOVCI`, `tf` = 1). -/
  | movt (rs cc rd : W32)
  -- Multiply-add family (COP1X, funct = op3 ‖ fmt3; unfused; Release 2).
  /-- `fd = (fs × ft) + fr`, single (funct 0x20). -/
  | maddS (fd fr fs ft : W32)
  /-- `fd = (fs × ft) − fr`, single (funct 0x28). -/
  | msubS (fd fr fs ft : W32)
  /-- `fd = −((fs × ft) + fr)`, single (funct 0x30). -/
  | nmaddS (fd fr fs ft : W32)
  /-- `fd = −((fs × ft) − fr)`, single (funct 0x38). -/
  | nmsubS (fd fr fs ft : W32)
  /-- `fd = (fs × ft) + fr`, double (funct 0x21). -/
  | maddD (fd fr fs ft : W32)
  /-- `fd = (fs × ft) − fr`, double (funct 0x29). -/
  | msubD (fd fr fs ft : W32)
  /-- `fd = −((fs × ft) + fr)`, double (funct 0x31). -/
  | nmaddD (fd fr fs ft : W32)
  /-- `fd = −((fs × ft) − fr)`, double (funct 0x39). -/
  | nmsubD (fd fr fs ft : W32)
  -- FP branches (COP1, rs = BC = 0x08; bits 20..18 cc, 17 nd, 16 tf).
  /-- Branch if `FCC[cc] = 0`, delay slot always executed. -/
  | bc1f (cc imm : W32)
  /-- Branch if `FCC[cc] = 1`, delay slot always executed. -/
  | bc1t (cc imm : W32)
  /-- Branch-likely if `FCC[cc] = 0`: delay slot nullified when not taken. -/
  | bc1fl (cc imm : W32)
  /-- Branch-likely if `FCC[cc] = 1`: delay slot nullified when not taken. -/
  | bc1tl (cc imm : W32)
  deriving Repr, DecidableEq

/-- Extract the 6-bit opcode field (bits 31..26), zero-extended to a `W32`. -/
def opcodeOf (w : W32) : W32 := (w.extractLsb 31 26).zeroExtend 32

/-- Extract the 5-bit `rs` field (bits 25..21), zero-extended to a `W32`. -/
def rsOf (w : W32) : W32 := (w.extractLsb 25 21).zeroExtend 32

/-- Extract the 5-bit `rt` field (bits 20..16), zero-extended to a `W32`. -/
def rtOf (w : W32) : W32 := (w.extractLsb 20 16).zeroExtend 32

/-- Extract the 5-bit `rd` field (bits 15..11), zero-extended to a `W32`. -/
def rdOf (w : W32) : W32 := (w.extractLsb 15 11).zeroExtend 32

/-- Extract the 5-bit `shamt` field (bits 10..6), zero-extended to a `W32`. -/
def shamtOf (w : W32) : W32 := (w.extractLsb 10 6).zeroExtend 32

/-- Extract the 6-bit `funct` field (bits 5..0), zero-extended to a `W32`. -/
def functOf (w : W32) : W32 := (w.extractLsb 5 0).zeroExtend 32

/-- Extract the raw 16-bit immediate/offset field (bits 15..0), zero-extended
to a `W32` with no sign interpretation applied. -/
def immOf (w : W32) : W32 := (w.extractLsb 15 0).zeroExtend 32

/-- Extract the raw 26-bit jump-target field (bits 25..0), zero-extended to a `W32`. -/
def targetOf (w : W32) : W32 := (w.extractLsb 25 0).zeroExtend 32

/-- Extract the FP condition-code field of a branch / `MOVCI` / `MOVCF`
(bits 20..18). -/
def ccOf (w : W32) : W32 := (w.extractLsb 20 18).zeroExtend 32

/-- Extract the `nd` bit (17) of an FP branch (must be 0 in `MOVCI`/`MOVCF`). -/
def ndOf (w : W32) : W32 := (w.extractLsb 17 17).zeroExtend 32

/-- Extract the `tf` bit (16) of an FP branch / `MOVCI` / `MOVCF`. -/
def tfOf (w : W32) : W32 := (w.extractLsb 16 16).zeroExtend 32

/-- Extract the condition-code field of `C.cond.fmt` (bits 10..8). -/
def fccOf (w : W32) : W32 := (w.extractLsb 10 8).zeroExtend 32

/-- Extract the `FC` field of a COP1 `fmt` word (bits 5..4): `11` (= 3)
exactly for `C.cond.fmt` (functs 0x30..0x3f). -/
def fcOf (w : W32) : W32 := (w.extractLsb 5 4).zeroExtend 32

/-- Extract bits 7..6 of a word (must be zero in `C.cond.fmt`). -/
def z76Of (w : W32) : W32 := (w.extractLsb 7 6).zeroExtend 32

/-- Extract the `CO` bit (25) of a COP0 word. -/
def coOf (w : W32) : W32 := (w.extractLsb 25 25).zeroExtend 32

/-- Extract the `cond` field of `C.cond.fmt` (bits 3..0). -/
def condOf (w : W32) : W32 := (w.extractLsb 3 0).zeroExtend 32

/-- Extract the 20-bit `code` field of `syscall`/`break` (bits 25..6). -/
def code20Of (w : W32) : W32 := (w.extractLsb 25 6).zeroExtend 32

/-- Extract the 10-bit `code` field of the register traps (bits 15..6). -/
def code10Of (w : W32) : W32 := (w.extractLsb 15 6).zeroExtend 32

/-- Extract the 19-bit `code` field of `wait` (bits 24..6). -/
def code19Of (w : W32) : W32 := (w.extractLsb 24 6).zeroExtend 32

/-- Word with a condition-code sub-field in the `rt` position, R-shaped:
`opcode` 31..26, `rs` 25..21, `cc` 20..18, `nd` 17, `tf` 16, `rd` 15..11,
`shamt` 10..6, `funct` 5..0 (`MOVCI`, `MOVCF.fmt`). -/
def mkCCR (opcode rs cc nd tf rd shamt funct : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 rs ||| field 3 18 cc ||| field 1 17 nd ||| field 1 16 tf |||
    field 5 11 rd ||| field 5 6 shamt ||| field 6 0 funct

/-- Word with a condition-code sub-field in the `rt` position, I-shaped
(`BC1F`/`BC1T`/`BC1FL`/`BC1TL`): `opcode`, `rs`, `cc`, `nd`, `tf`, `imm`. -/
def mkCCI (opcode rs cc nd tf imm : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 rs ||| field 3 18 cc ||| field 1 17 nd ||| field 1 16 tf |||
    field 16 0 imm

/-- `C.cond.fmt`-shaped word: `opcode` (COP1 = 0x11), `fmt`, `ft`, `fs`,
`cc` 10..8, `00` 7..6, `fc` 5..4 (`FC` = 3), `cond` 3..0. -/
def mkCmp (opcode fmt ft fs cc fc cond : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 fmt ||| field 5 16 ft ||| field 5 11 fs ||| field 3 8 cc |||
    field 2 4 fc ||| field 4 0 cond

/-- `syscall`/`break` word: SPECIAL, 20-bit `code` in bits 25..6, `funct`. -/
def mkCode20 (code funct : W32) : W32 := field 20 6 code ||| field 6 0 funct

/-- Register-trap word: SPECIAL, `rs`, `rt`, 10-bit `code` in bits 15..6,
`funct`. -/
def mkTrap (rs rt code funct : W32) : W32 :=
  field 5 21 rs ||| field 5 16 rt ||| field 10 6 code ||| field 6 0 funct

/-- `wait`-shaped word: `opcode` (COP0 = 0x10), `co` (bit 25, = 1), 19-bit
`code` in bits 24..6, `funct` (0x20). -/
def mkWait (opcode co code funct : W32) : W32 :=
  field 6 26 opcode ||| field 1 25 co ||| field 19 6 code ||| field 6 0 funct

/-- The coprocessor-0 registers this model implements, by `(rd, sel)`:
select 0 — `7` HWREna, `8` BadVAddr, `9` Count, `11` Compare, `12` Status, `13` Cause, `14` EPC,
`15` PRId, `16` Config, `30` ErrorEPC; select 1 — `15` EBase, `16` Config1. `decode`
accepts `mfc0`/`mtc0` only for these; every other pair does not decode and so
raises Reserved Instruction — a documented pin (the architecture leaves
access to an unimplemented CP0 register UNDEFINED/implementation-dependent). -/
def isModeledCp0Reg (rd sel : W32) : Bool :=
  (sel == 0#32 && (rd == 7#32 || rd == 8#32 || rd == 9#32 || rd == 11#32 || rd == 12#32 ||
      rd == 13#32 || rd == 14#32 || rd == 15#32 || rd == 16#32 || rd == 30#32)) ||
  (sel == 1#32 && (rd == 15#32 || rd == 16#32))

/-- `decodeIf c i` is `some i` when the must-be-zero check `c` holds, `none`
otherwise. Used by `decode` to reject non-canonical encodings. -/
def decodeIf (c : Bool) (i : Instruction) : Option Instruction :=
  if c then some i else none

/-- Decode a raw 32-bit instruction word into an `Instruction`, or `none` if
the word is not the canonical encoding of a modeled instruction (`step` then
raises Reserved Instruction). Ground truth: MD00086 Rev 2.50 encodings, as
summarised in `docs/spec/INSTRUCTION-REF.md`.

**Strict decoding.** Every field an encoding fixes to zero (or to another
constant) is checked; a word with a nonzero must-be-zero field does not
decode. Consequently `encode i = w` whenever `decode w = some i`, apart from
this one deliberately tolerated don't-care field, which `decode` ignores and
`encode` emits as zero:

* `jr`, `jalr` — the 5-bit `hint` field (bits 10..6). Bit 10 set is the
  Release 2 `jr.hb`/`jalr.hb` form; it executes as plain `jr`/`jalr` (this
  model has no instruction-hazard state to clear).

The software `code` fields of `syscall`/`break` (bits 25..6), the register
traps (bits 15..6) and `wait` (bits 24..6), and `sync`'s `stype`, are carried
in the constructors, so those round-trip exactly.

`sll` with `rd = 0` (`nop` = `sll $0,$0,0`, `ssnop` = shamt 1, `ehb` =
shamt 3) decodes as the ordinary `.sll` it is and executes as a no-op.

Encodings the manual calls UNPREDICTABLE are also rejected: `clz`/`clo` with
`rt ≠ rd`, `ext` with `lsb + msbd > 31`, `ins` with `msb < lsb`. -/
def decode (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let imm := immOf w
  let target := targetOf w
  let z (x : W32) : Bool := x == 0#32
  match (opcodeOf w).toNat with
  | 0x00 =>
    match (functOf w).toNat with
    | 0x20 => decodeIf (z shamt) (.add rs rt rd)
    | 0x21 => decodeIf (z shamt) (.addu rs rt rd)
    | 0x22 => decodeIf (z shamt) (.sub rs rt rd)
    | 0x23 => decodeIf (z shamt) (.subu rs rt rd)
    | 0x24 => decodeIf (z shamt) (.and rs rt rd)
    | 0x25 => decodeIf (z shamt) (.or rs rt rd)
    | 0x26 => decodeIf (z shamt) (.xor rs rt rd)
    | 0x27 => decodeIf (z shamt) (.nor rs rt rd)
    | 0x2a => decodeIf (z shamt) (.slt rs rt rd)
    | 0x2b => decodeIf (z shamt) (.sltu rs rt rd)
    | 0x0b => decodeIf (z shamt) (.movn rs rt rd)
    | 0x0a => decodeIf (z shamt) (.movz rs rt rd)
    | 0x00 => decodeIf (z rs) (.sll rd rt shamt)
    -- funct 0x02: bits 25..22 must be zero; bit 21 (`R`) selects `rotr`
    -- (MIPS32 Release 2) over `srl`.
    | 0x02 =>
      match rs.toNat with
      | 0 => some (.srl rd rt shamt)
      | 1 => some (.rotr rd rt shamt)
      | _ => none
    | 0x03 => decodeIf (z rs) (.sra rd rt shamt)
    | 0x04 => decodeIf (z shamt) (.sllv rd rt rs)
    -- funct 0x06: bits 10..7 must be zero; bit 6 (`R`) selects `rotrv` over
    -- `srlv`.
    | 0x06 =>
      match shamt.toNat with
      | 0 => some (.srlv rd rt rs)
      | 1 => some (.rotrv rd rt rs)
      | _ => none
    | 0x07 => decodeIf (z shamt) (.srav rd rt rs)
    | 0x18 => decodeIf (z rd && z shamt) (.mult rs rt)
    | 0x19 => decodeIf (z rd && z shamt) (.multu rs rt)
    | 0x1a => decodeIf (z rd && z shamt) (.div rs rt)
    | 0x1b => decodeIf (z rd && z shamt) (.divu rs rt)
    | 0x12 => decodeIf (z rs && z rt && z shamt) (.mflo rd)
    | 0x10 => decodeIf (z rs && z rt && z shamt) (.mfhi rd)
    | 0x11 => decodeIf (z rt && z rd && z shamt) (.mthi rs)
    | 0x13 => decodeIf (z rt && z rd && z shamt) (.mtlo rs)
    -- `jr`/`jalr`: the `hint` field (bits 10..6) is tolerated (see docstring).
    | 0x08 => decodeIf (z rt && z rd) (.jr rs)
    | 0x09 => decodeIf (z rt) (.jalr rs rd)
    -- `syscall`/`break`: bits 25..6 are the `code` field.
    | 0x0c => some (.syscall (code20Of w))
    | 0x0d => some (.break (code20Of w))
    -- `sync`: bits 25..11 must be zero; bits 10..6 are `stype`.
    | 0x0f => decodeIf (z rs && z rt && z rd) (.sync shamt)
    -- Traps: bits 15..6 are the `code` field.
    | 0x34 => some (.teq rs rt (code10Of w))
    | 0x36 => some (.tne rs rt (code10Of w))
    | 0x32 => some (.tlt rs rt (code10Of w))
    | 0x30 => some (.tge rs rt (code10Of w))
    | 0x33 => some (.tltu rs rt (code10Of w))
    | 0x31 => some (.tgeu rs rt (code10Of w))
    -- `MOVCI` (`movf`/`movt`): bits 20..18 cc, bit 17 zero, bit 16 tf,
    -- bits 10..6 zero.
    | 0x01 =>
      match (tfOf w).toNat with
      | 0 => decodeIf (z (ndOf w) && z shamt) (.movf rs (ccOf w) rd)
      | _ => decodeIf (z (ndOf w) && z shamt) (.movt rs (ccOf w) rd)
    | _ => none
  | 0x1c =>  -- SPECIAL2
    match (functOf w).toNat with
    -- `clo`/`clz`: the `rt` field must duplicate `rd` (MD00086: otherwise
    -- UNPREDICTABLE; rejected here).
    | 0x21 => decodeIf (rt == rd && z shamt) (.clo rs rd)
    | 0x20 => decodeIf (rt == rd && z shamt) (.clz rs rd)
    | 0x02 => decodeIf (z shamt) (.mul rs rt rd)
    | 0x00 => decodeIf (z rd && z shamt) (.madd rs rt)
    | 0x01 => decodeIf (z rd && z shamt) (.maddu rs rt)
    | 0x04 => decodeIf (z rd && z shamt) (.msub rs rt)
    | 0x05 => decodeIf (z rd && z shamt) (.msubu rs rt)
    | _ => none
  | 0x1f =>  -- SPECIAL3
    match (functOf w).toNat with
    | 0x20 =>  -- BSHFL: `rs` must be zero; the shamt sub-field selects
      match shamt.toNat with
      | 0x10 => decodeIf (z rs) (.seb rd rt)
      | 0x18 => decodeIf (z rs) (.seh rd rt)
      | 0x02 => decodeIf (z rs) (.wsbh rd rt)
      | _ => none
    -- `ext`: the `rd` field holds `msbd = size - 1`, `shamt` holds `lsb = pos`;
    -- `lsb + msbd > 31` is UNPREDICTABLE and rejected.
    | 0x00 => decodeIf (decide (shamt.toNat + rd.toNat ≤ 31)) (.ext rt rs shamt (rd + 1#32))
    -- `ins`: the `rd` field holds `msb = pos + size - 1`; `msb < lsb` is
    -- UNPREDICTABLE and rejected.
    | 0x04 => decodeIf (decide (shamt.toNat ≤ rd.toNat)) (.ins rt rs shamt (rd - shamt + 1#32))
    -- `rdhwr`: `rs` and bits 10..6 must be zero (pre-Release 6 has no `sel` field).
    | 0x3b => decodeIf (z rs && z shamt) (.rdhwr rt rd)
    | _ => none
  | 0x08 => some (.addi rs rt imm)
  | 0x09 => some (.addiu rs rt imm)
  | 0x0a => some (.slti rs rt imm)
  | 0x0b => some (.sltiu rs rt imm)
  | 0x0c => some (.andi rs rt imm)
  | 0x0d => some (.ori rs rt imm)
  | 0x0e => some (.xori rs rt imm)
  | 0x0f => decodeIf (z rs) (.lui rt imm)
  | 0x23 => some (.lw rs rt imm)
  | 0x2b => some (.sw rs rt imm)
  | 0x20 => some (.lb rs rt imm)
  | 0x24 => some (.lbu rs rt imm)
  | 0x21 => some (.lh rs rt imm)
  | 0x25 => some (.lhu rs rt imm)
  | 0x22 => some (.lwl rs rt imm)
  | 0x26 => some (.lwr rs rt imm)
  | 0x2a => some (.swl rs rt imm)
  | 0x2e => some (.swr rs rt imm)
  | 0x28 => some (.sb rs rt imm)
  | 0x29 => some (.sh rs rt imm)
  | 0x30 => some (.ll rs rt imm)
  | 0x38 => some (.sc rs rt imm)
  | 0x33 => some (.pref rs rt imm)
  | 0x04 => some (.beq rs rt imm)
  | 0x05 => some (.bne rs rt imm)
  | 0x06 => decodeIf (z rt) (.blez rs imm)
  | 0x07 => decodeIf (z rt) (.bgtz rs imm)
  -- Branch-likely (deprecated in MIPS32, removed in Release 6).
  | 0x14 => some (.beql rs rt imm)
  | 0x15 => some (.bnel rs rt imm)
  | 0x16 => decodeIf (z rt) (.blezl rs imm)
  | 0x17 => decodeIf (z rt) (.bgtzl rs imm)
  | 0x01 =>  -- REGIMM: the `rt` field selects
    match rt.toNat with
    | 0x00 => some (.bltz rs imm)
    | 0x01 => some (.bgez rs imm)
    | 0x10 => some (.bltzal rs imm)
    | 0x11 => some (.bgezal rs imm)
    | 0x02 => some (.bltzl rs imm)
    | 0x03 => some (.bgezl rs imm)
    | 0x12 => some (.bltzall rs imm)
    | 0x13 => some (.bgezall rs imm)
    | 0x08 => some (.tgei rs imm)
    | 0x09 => some (.tgeiu rs imm)
    | 0x0a => some (.tlti rs imm)
    | 0x0b => some (.tltiu rs imm)
    | 0x0c => some (.teqi rs imm)
    | 0x0e => some (.tnei rs imm)
    | 0x1f => some (.synci rs imm)
    | _ => none
  | 0x02 => some (.j target)
  | 0x03 => some (.jal target)
  | 0x10 =>  -- COP0
    -- CO sub-format: bit 25 set. `eret` requires bits 24..6 zero; `wait`'s
    -- bits 24..6 are its implementation-dependent `code` field.
    if coOf w == 1#32 then
      match (functOf w).toNat with
      | 0x18 => decodeIf (rs == 16#32 && z rt && z rd && z shamt) .eret
      | 0x20 => some (.wait (code19Of w))
      | _ => none
    else
    match rs.toNat with
    -- `mfc0`/`mtc0`: bits 10..3 must be zero, bits 2..0 are `sel`, and
    -- `(rd, sel)` must name a modeled register (`isModeledCp0Reg`).
    | 0x00 =>
      decodeIf (z shamt && decide ((functOf w).toNat < 8) && isModeledCp0Reg rd (functOf w))
        (.mfc0 rt rd (functOf w))
    | 0x04 =>
      decodeIf (z shamt && decide ((functOf w).toNat < 8) && isModeledCp0Reg rd (functOf w))
        (.mtc0 rt rd (functOf w))
    -- `MFMC0` (`di`/`ei`): `rd` = 12 (Status), bits 10..6 zero, bit 5 = `sc`,
    -- bits 4..0 zero.
    | 0x0b =>
      match (functOf w).toNat with
      | 0x00 => decodeIf (rd == 12#32 && z shamt) (.di rt)
      | 0x20 => decodeIf (rd == 12#32 && z shamt) (.ei rt)
      | _ => none
    | _ => none
  | 0x31 => some (.lwc1 rs rt imm)
  | 0x39 => some (.swc1 rs rt imm)
  | 0x35 => some (.ldc1 rs rt imm)
  | 0x3d => some (.sdc1 rs rt imm)
  | 0x11 =>  -- COP1
    match rs.toNat with
    -- `mfc1`/`mtc1`/`mfhc1`/`mthc1`/`cfc1`/`ctc1`: bits 10..0 must be zero.
    | 0x00 => decodeIf (z shamt && z (functOf w)) (.mfc1 rt rd)
    | 0x04 => decodeIf (z shamt && z (functOf w)) (.mtc1 rt rd)
    | 0x03 => decodeIf (z shamt && z (functOf w)) (.mfhc1 rt rd)
    | 0x07 => decodeIf (z shamt && z (functOf w)) (.mthc1 rt rd)
    | 0x02 => decodeIf (z shamt && z (functOf w)) (.cfc1 rt rd)
    | 0x06 => decodeIf (z shamt && z (functOf w)) (.ctc1 rt rd)
    | 0x08 =>  -- BC1: bits 20..18 cc, bit 17 nd (likely), bit 16 tf
      match (ndOf w).toNat, (tfOf w).toNat with
      | 0, 0 => some (.bc1f (ccOf w) imm)
      | 0, _ => some (.bc1t (ccOf w) imm)
      | _, 0 => some (.bc1fl (ccOf w) imm)
      | _, _ => some (.bc1tl (ccOf w) imm)
    -- fmt = S. Fields: ft = rt, fs = rd, fd = shamt. Unary operations require
    -- `ft = 0`. `C.cond.S` is recognised first (`FC` = bits 5..4 = 11) and
    -- requires bits 7..6 zero.
    | 0x10 =>
      if fcOf w == 3#32 then decodeIf (z (z76Of w)) (.cCondS (condOf w) (fccOf w) rd rt)
      else
      match (functOf w).toNat with
      | 0x00 => some (.addS shamt rd rt)
      | 0x01 => some (.subS shamt rd rt)
      | 0x02 => some (.mulS shamt rd rt)
      | 0x03 => some (.divS shamt rd rt)
      | 0x04 => decodeIf (z rt) (.sqrtS shamt rd)
      | 0x05 => decodeIf (z rt) (.absS shamt rd)
      | 0x06 => decodeIf (z rt) (.movS shamt rd)
      | 0x07 => decodeIf (z rt) (.negS shamt rd)
      | 0x0c => decodeIf (z rt) (.roundWS shamt rd)
      | 0x0d => decodeIf (z rt) (.truncWS shamt rd)
      | 0x0e => decodeIf (z rt) (.ceilWS shamt rd)
      | 0x0f => decodeIf (z rt) (.floorWS shamt rd)
      -- `MOVCF`: bits 20..18 cc, bit 17 zero, bit 16 tf
      | 0x11 =>
        match (tfOf w).toNat with
        | 0 => decodeIf (z (ndOf w)) (.movfS shamt rd (ccOf w))
        | _ => decodeIf (z (ndOf w)) (.movtS shamt rd (ccOf w))
      | 0x12 => some (.movzS shamt rd rt)
      | 0x13 => some (.movnS shamt rd rt)
      | 0x15 => decodeIf (z rt) (.recipS shamt rd)
      | 0x16 => decodeIf (z rt) (.rsqrtS shamt rd)
      | 0x21 => decodeIf (z rt) (.cvtDS shamt rd)
      | 0x24 => decodeIf (z rt) (.cvtWS shamt rd)
      | _ => none
    | 0x14 =>  -- fmt = W
      match (functOf w).toNat with
      | 0x20 => decodeIf (z rt) (.cvtSW shamt rd)
      | 0x21 => decodeIf (z rt) (.cvtDW shamt rd)
      | _ => none
    | 0x11 =>  -- fmt = D
      if fcOf w == 3#32 then decodeIf (z (z76Of w)) (.cCondD (condOf w) (fccOf w) rd rt)
      else
      match (functOf w).toNat with
      | 0x00 => some (.addD shamt rd rt)
      | 0x01 => some (.subD shamt rd rt)
      | 0x02 => some (.mulD shamt rd rt)
      | 0x03 => some (.divD shamt rd rt)
      | 0x04 => decodeIf (z rt) (.sqrtD shamt rd)
      | 0x05 => decodeIf (z rt) (.absD shamt rd)
      | 0x06 => decodeIf (z rt) (.movD shamt rd)
      | 0x07 => decodeIf (z rt) (.negD shamt rd)
      | 0x0c => decodeIf (z rt) (.roundWD shamt rd)
      | 0x0d => decodeIf (z rt) (.truncWD shamt rd)
      | 0x0e => decodeIf (z rt) (.ceilWD shamt rd)
      | 0x0f => decodeIf (z rt) (.floorWD shamt rd)
      | 0x11 =>
        match (tfOf w).toNat with
        | 0 => decodeIf (z (ndOf w)) (.movfD shamt rd (ccOf w))
        | _ => decodeIf (z (ndOf w)) (.movtD shamt rd (ccOf w))
      | 0x12 => some (.movzD shamt rd rt)
      | 0x13 => some (.movnD shamt rd rt)
      | 0x15 => decodeIf (z rt) (.recipD shamt rd)
      | 0x16 => decodeIf (z rt) (.rsqrtD shamt rd)
      | 0x20 => decodeIf (z rt) (.cvtSD shamt rd)
      | 0x24 => decodeIf (z rt) (.cvtWD shamt rd)
      | _ => none
    | _ => none
  | 0x13 =>  -- COP1X: base/fr = rs, index/ft = rt, fs/hint = rd, fd = shamt
    match (functOf w).toNat with
    | 0x00 => decodeIf (z rd) (.lwxc1 shamt rt rs)
    | 0x01 => decodeIf (z rd) (.ldxc1 shamt rt rs)
    | 0x08 => decodeIf (z shamt) (.swxc1 rd rt rs)
    | 0x09 => decodeIf (z shamt) (.sdxc1 rd rt rs)
    | 0x0f => decodeIf (z shamt) (.prefx rd rt rs)
    | 0x20 => some (.maddS shamt rs rd rt)
    | 0x21 => some (.maddD shamt rs rd rt)
    | 0x28 => some (.msubS shamt rs rd rt)
    | 0x29 => some (.msubD shamt rs rd rt)
    | 0x30 => some (.nmaddS shamt rs rd rt)
    | 0x31 => some (.nmaddD shamt rs rd rt)
    | 0x38 => some (.nmsubS shamt rs rd rt)
    | 0x39 => some (.nmsubD shamt rs rd rt)
    | _ => none
  | _ => none

/-- Encode an `Instruction` back into its raw 32-bit word: the canonical
encoding, with every reserved/don't-care field zero. `decode (encode i) =
some i` for well-formed `i` (fields in range); see
`Semantics/Specs/DecodeSpec.lean`. -/
def encode (i : Instruction) : W32 :=
  match i with
  | .add  rs rt rd => mkRT rs rt rd 0#32 0x20#32
  | .addu rs rt rd => mkRT rs rt rd 0#32 0x21#32
  | .sub  rs rt rd => mkRT rs rt rd 0#32 0x22#32
  | .subu rs rt rd => mkRT rs rt rd 0#32 0x23#32
  | .and  rs rt rd => mkRT rs rt rd 0#32 0x24#32
  | .or   rs rt rd => mkRT rs rt rd 0#32 0x25#32
  | .xor  rs rt rd => mkRT rs rt rd 0#32 0x26#32
  | .nor  rs rt rd => mkRT rs rt rd 0#32 0x27#32
  | .slt  rs rt rd => mkRT rs rt rd 0#32 0x2a#32
  | .sltu rs rt rd => mkRT rs rt rd 0#32 0x2b#32
  | .movn rs rt rd => mkRT rs rt rd 0#32 0x0b#32
  | .movz rs rt rd => mkRT rs rt rd 0#32 0x0a#32
  | .sll  rd rt shamt => mkRT 0#32 rt rd shamt 0x00#32
  | .srl  rd rt shamt => mkRT 0#32 rt rd shamt 0x02#32
  | .sra  rd rt shamt => mkRT 0#32 rt rd shamt 0x03#32
  | .sllv rd rt rs => mkRT rs rt rd 0#32 0x04#32
  | .srlv rd rt rs => mkRT rs rt rd 0#32 0x06#32
  | .srav rd rt rs => mkRT rs rt rd 0#32 0x07#32
  -- Rotate (MIPS32r2): `rs`/`shamt` field overloading, per the `.rotr`/
  -- `.rotrv` docstrings.
  | .rotr  rd rt sa => mkRT 0x01#32 rt rd sa 0x02#32
  | .rotrv rd rt rs => mkRT rs rt rd 0x01#32 0x06#32
  | .mult  rs rt => mkRT rs rt 0#32 0#32 0x18#32
  | .multu rs rt => mkRT rs rt 0#32 0#32 0x19#32
  | .div   rs rt => mkRT rs rt 0#32 0#32 0x1a#32
  | .divu  rs rt => mkRT rs rt 0#32 0#32 0x1b#32
  | .mflo rd => mkRT 0#32 0#32 rd 0#32 0x12#32
  | .mfhi rd => mkRT 0#32 0#32 rd 0#32 0x10#32
  | .mthi rs => mkRT rs 0#32 0#32 0#32 0x11#32
  | .mtlo rs => mkRT rs 0#32 0#32 0#32 0x13#32
  | .jr   rs => mkRT rs 0#32 0#32 0#32 0x08#32
  | .jalr rs rd => mkRT rs 0#32 rd 0#32 0x09#32
  -- SPECIAL2: duplicate rd into the rt-position field per the real encoding.
  | .clo rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x21#32
  | .clz rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x20#32
  | .mul rs rt rd => (0x1c#32 <<< 26) ||| mkRT rs rt rd 0#32 0x02#32
  | .madd  rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x00#32
  | .maddu rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x01#32
  | .msub  rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x04#32
  | .msubu rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x05#32
  -- SPECIAL3 BSHFL: rs fixed 0, shamt-position field selects seb/seh/wsbh.
  | .seb rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x10#32 0x20#32
  | .seh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x18#32 0x20#32
  | .wsbh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x02#32 0x20#32
  -- SPECIAL3 bitfield extract/insert: `pos` is the raw `shamt` field for
  -- both; the raw `rd`-position field is `size - 1` for `ext` ("msbd") but
  -- `pos + size - 1` for `ins` ("msb") -- see the `.ext`/`.ins` docstrings.
  | .ext rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (size - 1#32) pos 0x00#32
  | .ins rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (pos + size - 1#32) pos 0x04#32
  | .rdhwr rt rd => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0#32 0x3b#32
  | .addi  rs rt imm => mkIT 0x08#32 rs rt imm
  | .addiu rs rt imm => mkIT 0x09#32 rs rt imm
  | .slti  rs rt imm => mkIT 0x0a#32 rs rt imm
  | .sltiu rs rt imm => mkIT 0x0b#32 rs rt imm
  | .andi  rs rt imm => mkIT 0x0c#32 rs rt imm
  | .ori   rs rt imm => mkIT 0x0d#32 rs rt imm
  | .xori  rs rt imm => mkIT 0x0e#32 rs rt imm
  | .lui   rt imm    => mkIT 0x0f#32 0#32 rt imm
  | .lw rs rt imm => mkIT 0x23#32 rs rt imm
  | .sw rs rt imm => mkIT 0x2b#32 rs rt imm
  | .lb rs rt imm => mkIT 0x20#32 rs rt imm
  | .lbu rs rt imm => mkIT 0x24#32 rs rt imm
  | .lh rs rt imm => mkIT 0x21#32 rs rt imm
  | .lhu rs rt imm => mkIT 0x25#32 rs rt imm
  | .sh rs rt imm => mkIT 0x29#32 rs rt imm
  | .sb rs rt imm => mkIT 0x28#32 rs rt imm
  | .ll rs rt imm => mkIT 0x30#32 rs rt imm
  | .sc rs rt imm => mkIT 0x38#32 rs rt imm
  | .lwl rs rt imm => mkIT 0x22#32 rs rt imm
  | .lwr rs rt imm => mkIT 0x26#32 rs rt imm
  | .swl rs rt imm => mkIT 0x2a#32 rs rt imm
  | .swr rs rt imm => mkIT 0x2e#32 rs rt imm
  | .beq rs rt imm => mkIT 0x04#32 rs rt imm
  | .bne rs rt imm => mkIT 0x05#32 rs rt imm
  | .blez rs imm => mkIT 0x06#32 rs 0#32 imm
  | .bgtz rs imm => mkIT 0x07#32 rs 0#32 imm
  | .bltz   rs imm => mkIT 0x01#32 rs 0x00#32 imm
  | .bgez   rs imm => mkIT 0x01#32 rs 0x01#32 imm
  | .bltzal rs imm => mkIT 0x01#32 rs 0x10#32 imm
  | .bgezal rs imm => mkIT 0x01#32 rs 0x11#32 imm
  | .beql rs rt imm => mkIT 0x14#32 rs rt imm
  | .bnel rs rt imm => mkIT 0x15#32 rs rt imm
  | .blezl rs imm => mkIT 0x16#32 rs 0#32 imm
  | .bgtzl rs imm => mkIT 0x17#32 rs 0#32 imm
  | .bltzl   rs imm => mkIT 0x01#32 rs 0x02#32 imm
  | .bgezl   rs imm => mkIT 0x01#32 rs 0x03#32 imm
  | .bltzall rs imm => mkIT 0x01#32 rs 0x12#32 imm
  | .bgezall rs imm => mkIT 0x01#32 rs 0x13#32 imm
  | .teqi   rs imm => mkIT 0x01#32 rs 0x0c#32 imm
  | .tnei   rs imm => mkIT 0x01#32 rs 0x0e#32 imm
  | .tgei   rs imm => mkIT 0x01#32 rs 0x08#32 imm
  | .tgeiu  rs imm => mkIT 0x01#32 rs 0x09#32 imm
  | .tlti   rs imm => mkIT 0x01#32 rs 0x0a#32 imm
  | .tltiu  rs imm => mkIT 0x01#32 rs 0x0b#32 imm
  | .synci  rs imm => mkIT 0x01#32 rs 0x1f#32 imm
  | .j   target => (0x02#32 <<< 26) ||| mkJT target
  | .jal target => (0x03#32 <<< 26) ||| mkJT target
  | .syscall code => mkCode20 code 0x0c#32
  | .teq rs rt code => mkTrap rs rt code 0x34#32
  | .tne rs rt code => mkTrap rs rt code 0x36#32
  | .tlt rs rt code => mkTrap rs rt code 0x32#32
  | .tge rs rt code => mkTrap rs rt code 0x30#32
  | .tltu rs rt code => mkTrap rs rt code 0x33#32
  | .tgeu rs rt code => mkTrap rs rt code 0x31#32
  | .break code => mkCode20 code 0x0d#32
  -- sync: no stored `stype` field, so this always encodes `stype = 0`
  -- (the default "complete barrier"), same simplification as `break`'s
  -- unmodeled "code" field.
  | .sync stype => mkRT 0#32 0#32 0#32 stype 0x0f#32
  | .pref rs hint imm => mkIT 0x33#32 rs hint imm
  -- Coprocessor 0 (CP0). Same opcode-OR convention as the COP1 cases below.
  | .mfc0 rt rd sel => (0x10#32 <<< 26) ||| mkRT 0x00#32 rt rd 0#32 sel
  | .mtc0 rt rd sel => (0x10#32 <<< 26) ||| mkRT 0x04#32 rt rd 0#32 sel
  | .di rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 12#32 0#32 0x00#32
  | .ei rt => (0x10#32 <<< 26) ||| mkRT 0x0b#32 rt 12#32 0#32 0x20#32
  | .eret => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32
  | .wait code => mkWait 0x10#32 1#32 code 0x20#32
  -- Coprocessor 1 (FPU). `mkRT` leaves the opcode field 0 (correct for
  -- plain R-type), so the COP1 cases OR in opcode 0x11 explicitly, the same
  -- way `.j`/`.jal` OR in their opcode over `mkJT`'s target-only field.
  | .mfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x00#32 rt fs 0#32 0#32
  | .mtc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x04#32 rt fs 0#32 0#32
  | .mfhc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x03#32 rt fs 0#32 0#32
  | .mthc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x07#32 rt fs 0#32 0#32
  | .cfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x02#32 rt fs 0#32 0#32
  | .ctc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x06#32 rt fs 0#32 0#32
  | .lwc1 rs ft imm => mkIT 0x31#32 rs ft imm
  | .swc1 rs ft imm => mkIT 0x39#32 rs ft imm
  | .ldc1 rs ft imm => mkIT 0x35#32 rs ft imm
  | .sdc1 rs ft imm => mkIT 0x3d#32 rs ft imm
  | .lwxc1 fd index base => (0x13#32 <<< 26) ||| mkRT base index 0#32 fd 0x00#32
  | .ldxc1 fd index base => (0x13#32 <<< 26) ||| mkRT base index 0#32 fd 0x01#32
  | .swxc1 fs index base => (0x13#32 <<< 26) ||| mkRT base index fs 0#32 0x08#32
  | .sdxc1 fs index base => (0x13#32 <<< 26) ||| mkRT base index fs 0#32 0x09#32
  | .prefx hint index base => (0x13#32 <<< 26) ||| mkRT base index hint 0#32 0x0f#32
  | .addS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x00#32
  | .subS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x01#32
  | .mulS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x02#32
  | .divS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x03#32
  | .sqrtS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x04#32
  | .absS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x05#32
  | .movS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x06#32
  | .negS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x07#32
  | .recipS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x15#32
  | .rsqrtS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x16#32
  | .roundWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0c#32
  | .truncWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0d#32
  | .ceilWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0e#32
  | .floorWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0f#32
  | .cvtWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x24#32
  | .cCondS cond cc fs ft => mkCmp 0x11#32 0x10#32 ft fs cc 3#32 cond
  | .movfS fd fs cc => mkCCR 0x11#32 0x10#32 cc 0#32 0#32 fs fd 0x11#32
  | .movtS fd fs cc => mkCCR 0x11#32 0x10#32 cc 0#32 1#32 fs fd 0x11#32
  | .movzS fd fs rt => (0x11#32 <<< 26) ||| mkRT 0x10#32 rt fs fd 0x12#32
  | .movnS fd fs rt => (0x11#32 <<< 26) ||| mkRT 0x10#32 rt fs fd 0x13#32
  | .addD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x00#32
  | .subD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x01#32
  | .mulD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x02#32
  | .divD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x03#32
  | .sqrtD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x04#32
  | .absD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x05#32
  | .movD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x06#32
  | .negD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x07#32
  | .recipD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x15#32
  | .rsqrtD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x16#32
  | .roundWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0c#32
  | .truncWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0d#32
  | .ceilWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0e#32
  | .floorWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x0f#32
  | .cvtWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x24#32
  | .cCondD cond cc fs ft => mkCmp 0x11#32 0x11#32 ft fs cc 3#32 cond
  | .movfD fd fs cc => mkCCR 0x11#32 0x11#32 cc 0#32 0#32 fs fd 0x11#32
  | .movtD fd fs cc => mkCCR 0x11#32 0x11#32 cc 0#32 1#32 fs fd 0x11#32
  | .movzD fd fs rt => (0x11#32 <<< 26) ||| mkRT 0x11#32 rt fs fd 0x12#32
  | .movnD fd fs rt => (0x11#32 <<< 26) ||| mkRT 0x11#32 rt fs fd 0x13#32
  | .cvtDS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x21#32
  | .cvtSD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x20#32
  | .cvtSW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x20#32
  | .cvtDW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x21#32
  | .movf rs cc rd => mkCCR 0#32 rs cc 0#32 0#32 rd 0#32 0x01#32
  | .movt rs cc rd => mkCCR 0#32 rs cc 0#32 1#32 rd 0#32 0x01#32
  | .maddS fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x20#32
  | .maddD fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x21#32
  | .msubS fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x28#32
  | .msubD fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x29#32
  | .nmaddS fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x30#32
  | .nmaddD fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x31#32
  | .nmsubS fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x38#32
  | .nmsubD fd fr fs ft => (0x13#32 <<< 26) ||| mkRT fr ft fs fd 0x39#32
  | .bc1f cc imm => mkCCI 0x11#32 0x08#32 cc 0#32 0#32 imm
  | .bc1t cc imm => mkCCI 0x11#32 0x08#32 cc 0#32 1#32 imm
  | .bc1fl cc imm => mkCCI 0x11#32 0x08#32 cc 1#32 0#32 imm
  | .bc1tl cc imm => mkCCI 0x11#32 0x08#32 cc 1#32 1#32 imm

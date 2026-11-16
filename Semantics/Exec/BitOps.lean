import Semantics.Exec.Base

/-!
# Exec.BitOps — bit counting, sign extension, byte swap and bit-field instructions

The execution of bit counting, sign extension, byte swap and bit-field instructions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

-- BEGIN R6-4
/-- `BITSWAP` (MD00086 Vol II-A Rev 6.06, p.92): the bits of each byte reversed, each byte in place;
by swapping adjacent bits, then bit pairs, then nibbles within every byte. -/
def bitswapWord (v : W32) : W32 :=
  let v := ((v >>> 1) &&& 0x55555555#32) ||| ((v &&& 0x55555555#32) <<< 1)
  let v := ((v >>> 2) &&& 0x33333333#32) ||| ((v &&& 0x33333333#32) <<< 2)
  ((v >>> 4) &&& 0x0F0F0F0F#32) ||| ((v &&& 0x0F0F0F0F#32) <<< 4)
-- END R6-4

/-- The effect of bit counting, sign extension, byte swap and bit-field instructions; `none` for every other instruction. -/
def execBitOps (s : State) : Instruction → Option State
  -- SPECIAL2 bit-count (MIPS32)
  | .clo rs rd => some <|
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingOnes (readReg s (regIdx rs)))))
  | .clz rs rd => some <|
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingZeros (readReg s (regIdx rs)))))
  -- SPECIAL3 BSHFL sign-extend (MIPS32r2)
  | .seb rd rt => some <|
    mkNext s (writeReg s (regIdx rd) (signExtLowByte (readReg s (regIdx rt))))
  | .seh rd rt => some <|
    mkNext s (writeReg s (regIdx rd) (signExt16 (readReg s (regIdx rt))))
  -- SPECIAL3 BSHFL word-swap-bytes-within-halfwords (MIPS32r2): swap the
  -- two bytes of each 16-bit half of `$rt` independently; the halfwords
  -- themselves stay in their original word positions (not a full 32-bit
  -- byte-reverse -- that's `wsbh` + `rotr 16`, not modeled as a single op).
  | .wsbh rd rt => some <|
    let v := readReg s (regIdx rt)
    let b0 := v &&& 0xff#32
    let b1 := (v >>> 8) &&& 0xff#32
    let b2 := (v >>> 16) &&& 0xff#32
    let b3 := (v >>> 24) &&& 0xff#32
    let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
    mkNext s (writeReg s (regIdx rd) result)
  -- SPECIAL3 bitfield extract/insert (MIPS32r2; MD00086 Vol II-A Rev 6.06,
  -- EXT p.183, INS p.192-193). The constructor's `pos`/`size` are mapped to
  -- the diagram's 5-bit fields as `encode` writes them: EXT `lsb = pos`,
  -- `msbd = size - 1`; INS `lsb = pos`, `msb = pos + size - 1` (each mod 32).
  -- The UNPREDICTABLE ranges (EXT `lsb + msbd > 31`, INS `lsb > msb`) raise
  -- Reserved Instruction, as `decode` does for such words (SPEC-NOTES §11).
  | .ext rt rs pos size => some <|
    let lsb := (pos &&& 31#32).toNat
    let msbd := ((size - 1#32) &&& 31#32).toNat
    if lsb + msbd > 31 then takeException s excCodeRI
    else
      let field := (readReg s (regIdx rs) >>> lsb) &&& lowBitsMask (msbd + 1)
      mkNext s (writeReg s (regIdx rt) field)
  | .ins rt rs pos size => some <|
    let lsb := (pos &&& 31#32).toNat
    let msb := ((pos + size - 1#32) &&& 31#32).toNat
    if lsb > msb then takeException s excCodeRI
    else
      let mask := lowBitsMask (msb + 1 - lsb)
      let srcField := (readReg s (regIdx rs) &&& mask) <<< lsb
      let clearMask := ~~~(mask <<< lsb)
      let newVal := (readReg s (regIdx rt) &&& clearMask) ||| srcField
      mkNext s (writeReg s (regIdx rt) newVal)
  -- BEGIN R6-4
  -- ALIGN (p.39): `($rt << 8·bp) | ($rs >> 8·(4-bp))`, logical 32-bit shifts (`bp = 0` gives `$rt`).
  | .align rs rt rd bp => some <|
    let b := (bp &&& 3#32).toNat
    mkNext s (writeReg s (regIdx rd)
      ((readReg s (regIdx rt) <<< (8 * b)) ||| (readReg s (regIdx rs) >>> (8 * (4 - b)))))
  -- BITSWAP (p.92).
  | .bitswap rd rt => some <|
    mkNext s (writeReg s (regIdx rd) (bitswapWord (readReg s (regIdx rt))))
  -- END R6-4
  | _ => none

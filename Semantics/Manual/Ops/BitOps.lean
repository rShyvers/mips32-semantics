import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.BitOps — count leading bits, sign extension, byte swap, bit fields (MD00086 Vol II-A Rev 6.06)
-/

namespace Manual.Ops

open Manual

/-- The loop `for i in 31 .. 0 … if GPR[rs]i = b then temp ← 31 - i; break` of `CLO`/`CLZ`: the
first index `i`, counting down from 31, at which `x_i = b`. -/
private def firstFrom31 (x : W32) (b : Bool) : Option Nat :=
  (List.range 32).reverse.find? (fun i => bit x i == b)

/-- **CLO rd, rs** — MD00086 Vol II-A Rev 6.06, CLO, p.134 (Release 6 diagram: SPECIAL, `rt = 00000`, `sa = 00001`).
```
temp ← 32
for i in 31 .. 0
   if GPR[rs]i = 0 then
      temp ← 31 - i
      break
   endif
endfor
GPR[rd] ← temp
```
The pre-Release 6 restriction on `rt` and `rd` does not apply: "Release 6's new instruction encoding
does not contain an rt field" (Restrictions, p.134). -/
def CLO (rs rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  -- temp ← 32; for i in 31 .. 0: if GPR[rs]i = 0 then temp ← 31 - i; break
  let temp : Nat := match firstFrom31 x false with
    | some i => 31 - i
    | none => 32
  -- GPR[rd] ← temp
  setGPR (reg rd) (BitVec.ofNat 32 temp)

/-- **CLZ rd, rs** — MD00086 Vol II-A Rev 6.06, CLZ, p.135 (Release 6 diagram: SPECIAL, `rt = 00000`, `sa = 00001`).
```
temp ← 32
for i in 31 .. 0
   if GPR[rs]i = 1 then
      temp ← 31 - i
      break
   endif
endfor
GPR[rd] ← temp
```
As for `CLO`, the Release 6 encoding has no `rt` field (p.135). -/
def CLZ (rs rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  -- temp ← 32; for i in 31 .. 0: if GPR[rs]i = 1 then temp ← 31 - i; break
  let temp : Nat := match firstFrom31 x true with
    | some i => 31 - i
    | none => 32
  -- GPR[rd] ← temp
  setGPR (reg rd) (BitVec.ofNat 32 temp)

/-- **SEB rd, rt** — MD00086 Vol II-A Rev 6.06, SEB, p.365.
```
GPR[rd] ← sign_extend(GPR[rt]7..0)
``` -/
def SEB (rd rt : W32) : Pseudo Unit := do
  -- GPR[rd] ← sign_extend(GPR[rt]7..0)
  setGPR (reg rd) (sign_extend (bits (← GPR (reg rt)) 7 0))

/-- **SEH rd, rt** — MD00086 Vol II-A Rev 6.06, SEH, p.366.
```
GPR[rd] ← signextend(GPR[rt]15..0)
``` -/
def SEH (rd rt : W32) : Pseudo Unit := do
  -- GPR[rd] ← signextend(GPR[rt]15..0)
  setGPR (reg rd) (sign_extend (bits (← GPR (reg rt)) 15 0))

/-- **WSBH rd, rt** — MD00086 Vol II-A Rev 6.06, WSBH, p.445.
```
GPR[rd] ← GPR[rs]23..16 || GPR[rs]31..24 || GPR[rs]7..0 || GPR[rs]15..8
```
The printed Operation names `GPR[rs]`; the format diagram has no `rs` operand (the field is `0`) and the
Description says "Within each halfword of GPR rt the bytes are swapped", so the source is `GPR[rt]`
(a misprint in the page, SPEC-NOTES §11). -/
def WSBH (rd rt : W32) : Pseudo Unit := do
  let x ← GPR (reg rt)
  -- GPR[rd] ← GPR[rt]23..16 || GPR[rt]31..24 || GPR[rt]7..0 || GPR[rt]15..8
  setGPR (reg rd) ((bits x 23 16 ++ bits x 31 24 ++ bits x 7 0 ++ bits x 15 8).setWidth 32)

/-- **EXT rt, rs, pos, size** — MD00086 Vol II-A Rev 6.06, EXT, p.183 (image-only page, read from the
PDF).
```
if (lsb + msbd) > 31 then
   UNPREDICTABLE
endif
temp ← 032-(msbd+1) || GPR[rs]msbd+lsb..lsb
GPR[rt] ← temp
```
With `msbd ← size-1` and `lsb ← pos` (Description, p.183), read as the 5-bit fields of the diagram
(`Manual.enc` writes `size - 1` and `pos` there, so a constructor `size = 0` is `msbd = 31`). `Oracle.extOutOfRange` resolves the
UNPREDICTABLE case (`unpredictableOr`): `.proceed` evaluates the formula with bits above 31 read as
0; a signal or another state replaces the rest of the Operation. -/
def EXT (rt rs pos size : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  -- msbd ← size-1 (the 5-bit msbd field of the diagram, as `enc` writes it)
  let msbd := (low (size - 1#32) 5).toNat
  -- lsb ← pos (the 5-bit lsb field)
  let lsb := (low pos 5).toNat
  let body : Pseudo Unit := do
    -- temp ← 0^(32-(msbd+1)) || GPR[rs]msbd+lsb..lsb
    let temp : W32 := (0#(32 - (msbd + 1)) ++ low (x >>> lsb) (msbd + 1)).setWidth 32
    -- GPR[rt] ← temp
    setGPR (reg rt) temp
  -- if (lsb + msbd) > 31 then UNPREDICTABLE endif
  if lsb + msbd > 31 then unpredictableOr ((← Pseudo.oracle).extOutOfRange (← Pseudo.get)) body
  else body

/-- **INS rt, rs, pos, size** — MD00086 Vol II-A Rev 6.06, INS, p.192-193 (p.192 image-only, read from
the PDF).
```
if lsb > msb then
   UNPREDICTABLE
endif
GPR[rt] ← GPR[rt]31..msb+1 || GPR[rs]msb-lsb..0 || GPR[rt]lsb-1..0
```
With `msb ← pos+size-1` and `lsb ← pos` (Description, p.192), read as the 5-bit fields of the diagram
(as `Manual.enc` writes them). `Oracle.insLsbAboveMsb` resolves the UNPREDICTABLE case
(`unpredictableOr`); when it says `.proceed` the formula is evaluated as written (a negative width is
the empty string). -/
def INS (rt rs pos size : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let t ← GPR (reg rt)
  -- msb ← pos+size-1 (the 5-bit msb field of the diagram, as `enc` writes it)
  let msb : Int := ((low (pos + size - 1#32) 5).toNat : Int)
  -- lsb ← pos (the 5-bit lsb field)
  let lsb := (low pos 5).toNat
  let body : Pseudo Unit := do
    -- GPR[rt] ← GPR[rt]31..msb+1 || GPR[rs]msb-lsb..0 || GPR[rt]lsb-1..0
    let temp : W32 :=
      (low (t >>> (msb + 1).toNat) (31 - msb).toNat ++ low x (msb - lsb + 1).toNat ++
        low t lsb).setWidth 32
    setGPR (reg rt) temp
  -- if lsb > msb then UNPREDICTABLE endif
  if (lsb : Int) > msb then unpredictableOr ((← Pseudo.oracle).insLsbAboveMsb (← Pseudo.get)) body
  else body

/-- **ALIGN rd, rs, rt, bp** — MD00086 Vol II-A Rev 6.06, ALIGN, p.39 (an image-only page: diagram,
Description and Operation read from the PDF).
```
tmp_rt_hi ← unsigned_word(GPR[rt]) << (8*bp)
tmp_rs_lo ← unsigned_word(GPR[rs]) >> (8*(4-bp))
tmp ← tmp_rt_hi or tmp_rt_lo
GPR[rd] ← tmp
```
"The 32-bit word in GPR rt is left shifted as a 32-bit value by bp byte positions. The 32-bit word in
register rs is right shifted as a 32-bit value by (4-bp) byte positions. These shifts are logical
shifts, zero-filling" (Description, p.39): the shifts are on 32-bit values (`bp = 0` shifts `GPR[rs]`
out entirely: "Executing ALIGN with shift count bp=0 acts like a register to register move", p.39).
The Operation's `tmp_rt_lo` is a misprint of `tmp_rs_lo` (the only other name defined). -/
def ALIGN (rs rt rd bp : W32) : Pseudo Unit := do
  let b := (low bp 2).toNat
  -- tmp_rt_hi ← unsigned_word(GPR[rt]) << (8*bp)
  let tmp_rt_hi := (← GPR (reg rt)) <<< (8 * b)
  -- tmp_rs_lo ← unsigned_word(GPR[rs]) >> (8*(4-bp))
  let tmp_rs_lo := (← GPR (reg rs)) >>> (8 * (4 - b))
  -- tmp ← tmp_rt_hi or tmp_rs_lo
  let tmp := tmp_rt_hi ||| tmp_rs_lo
  -- GPR[rd] ← tmp
  setGPR (reg rd) tmp

/-- `reverse_bits_in_byte(inbyte)` (BITSWAP, p.92):
```
outbyte7 ← inbyte0
outbyte6 ← inbyte1
...
outbyte0 ← inbyte7
return outbyte
```
written as the string `outbyte7 || ... || outbyte0`. -/
def reverse_bits_in_byte (inbyte : BitVec 8) : BitVec 8 :=
  BitVec.ofBool (bit inbyte 0) ++ BitVec.ofBool (bit inbyte 1) ++ BitVec.ofBool (bit inbyte 2) ++
    BitVec.ofBool (bit inbyte 3) ++ BitVec.ofBool (bit inbyte 4) ++ BitVec.ofBool (bit inbyte 5) ++
    BitVec.ofBool (bit inbyte 6) ++ BitVec.ofBool (bit inbyte 7)

/-- **BITSWAP rd, rt** — MD00086 Vol II-A Rev 6.06, BITSWAP, p.92.
```
for i in 0 to 3 do      /* for all bytes in 32-bit GPR width */
   tmp.byte(i) ← reverse_bits_in_byte( GPR[rt].byte(i) )
endfor
GPR[rd] ← tmp
``` -/
def BITSWAP (rd rt : W32) : Pseudo Unit := do
  let x ← GPR (reg rt)
  -- for i in 0 to 3 do tmp.byte(i) ← reverse_bits_in_byte( GPR[rt].byte(i) )
  let tmp : W32 :=
    reverse_bits_in_byte (x.extractLsb' 24 8) ++ reverse_bits_in_byte (x.extractLsb' 16 8) ++
      reverse_bits_in_byte (x.extractLsb' 8 8) ++ reverse_bits_in_byte (x.extractLsb' 0 8)
  -- GPR[rd] ← tmp
  setGPR (reg rd) tmp

end Manual.Ops

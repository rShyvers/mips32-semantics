import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.VP — DVP and EVP (MD00086 Vol II-A Rev 6.06)

The Release 6 virtual-processor instructions. Both are in the COP0 encoding space: the Coprocessor
Unusable check ("If access to Coprocessor 0 is not enabled, a Coprocessor Unusable Exception is
signaled", DVP Restrictions p.172, EVP Restrictions p.181) is made for the whole space before the
Operation runs (`Manual.Cycle`).

Their Operation (DVP p.173, EVP p.182) reads and writes `VPControl` and acts on the other virtual
processors of the core, which exist only with multi-threading support. The Description of each page
settles the case without it: "For implementations that do not support multi-threading
(Config5VP=0), this instruction must be treated as a NOP instruction" (DVP p.172, EVP p.181). This
profile has no multi-threading: `Config5.VP` (bit 7) is 0 ("No multi-threading support. There is
only one virtual core/physical core. There are no COP0 or ISA extensions for multi-threading",
MD00090 Vol III Rev 6.02 Table 9.69, p.263), as the pinned read-only part of `Config5` gives it
(`Impl.Config5Fixed`, `Impl.WF`). So the transcription is the NOP the Description requires, and
`GPR[rt]` is not written.
-/

namespace Manual.Ops

open Manual

/-- **DVP rt** — MD00086 Vol II-A Rev 6.06, DVP, p.172-173. With `Config5VP = 0` (module doc):
"this instruction must be treated as a NOP instruction" (p.172). -/
def DVP (_rt : W32) : Pseudo Unit :=
  pure ()

/-- **EVP rt** — MD00086 Vol II-A Rev 6.06, EVP, p.181-182. With `Config5VP = 0` (module doc):
"this instruction must be treated as a NOP instruction" (p.181). -/
def EVP (_rt : W32) : Pseudo Unit :=
  pure ()

end Manual.Ops

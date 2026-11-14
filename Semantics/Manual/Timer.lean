import Semantics.Manual.CP0

/-!
# Manual.Timer — Count and Compare

MD00090 Vol III Rev 6.02 §9.27 `Count` (p.183) and §9.30 `Compare` (p.187); `Cause.DC` and
`Cause.TI` (Table 9.52, p.209-210).
-/

namespace Manual

/-- **The timer's part of one instruction time.** `Count` "acts as a timer, incrementing at a
constant rate, whether or not an instruction is executed, retired, or any forward progress is made
through the pipeline. The rate at which the counter increments is implementation-dependent" (§9.27,
p.183): `Impl.CountIncrement` per instruction time, unless `Cause.DC = 1` ("Disable Count register",
Table 9.52, p.210). "When the value of the Count register equals the value of the Compare register,
an interrupt request is made ... the presence of the interrupt is visible to software via the CauseTI
bit" (§9.30, p.187): `TI` is set when the new `Count` equals `Compare` and stays set until a write to
`Compare` clears it (`CPRWrite`).

**Pin (implementation-dependent placement):** the timer advances after the instruction of the
instruction time, so the instruction reads the `Count` the instruction time started with, and a
request raised by this tick is seen by the next instruction time's interrupt check. -/
def TimerTick (i : Impl) (a : Arch) : Arch :=
  let c := if CauseDC a then a.Count else a.Count + i.CountIncrement
  { a with Count := c, CauseTI := a.CauseTI || c == a.Compare }

end Manual

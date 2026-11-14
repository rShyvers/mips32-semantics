import Semantics.Manual.Exceptions

/-!
# Manual.Interrupts — interrupt compatibility mode

MD00090 Vol III Rev 6.02 §6.1 (p.72) and §6.1.1.1, Table 6.2 (p.73). Vectored Interrupt and EIC
modes are optional and absent (`Config3` does not exist: `Config1.M = 0`; `IntCtl.VS = 0`).
-/

namespace Manual

/-- **The requests for interrupt service** (§6.1.1.1, Table 6.2, p.73, "Request for Interrupt
Service in Interrupt Compatibility Mode"): request `i` is "CauseIPi and StatusIMi" (`i` = 7 … 0),
with `Cause.IP` as read (`CauseRead`: software requests IP1..IP0, hardware HW5..HW0 in IP7..IP2, the
timer merged). -/
def InterruptRequests (i : Impl) (a : Arch) : BitVec 8 :=
  (CauseRead i a).extractLsb' 8 8 &&& StatusIM a

/-- **Interrupts are enabled** (§6.1, p.72): "The IE bit in the Status register is a one", "The EXL
and ERL bits in the Status register are both zero" (no EJTAG: "The DM bit in the Debug register is a
zero" holds). -/
def InterruptsEnabled (a : Arch) : Bool := StatusIE a && !StatusEXL a && !StatusERL a

/-- **An interrupt is taken** (§6.1, p.72): "An interrupt is only taken when all of the following
are true: A specific request for interrupt service is made ... The IE bit ... is a one ... The EXL and
ERL bits ... are both zero". Interrupts are asynchronous and have "the highest priority relative to
the next instruction" (Table 6.7, p.84), below only Reset, Soft Reset, NMI, Machine Check and the
EJTAG exceptions (Table 6.6, p.83), none of which this profile raises from an instruction time. -/
def InterruptTaken (i : Impl) (a : Arch) : Bool :=
  InterruptsEnabled a && InterruptRequests i a ≠ 0#8

/-- **The lower power mode of `WAIT`** without an enabled interrupt (MD00086 Vol II-A Rev 6.06, WAIT,
p.442): "The pipeline is restarted when an external event, such as an interrupt or external request
occurs"; "It is implementation-dependent whether the pipeline restarts when a non-enabled interrupt
is requested" (`Impl.WaitRestartsOnNotEnabled`). Restarting takes the instruction time; execution
continues at `PC`, the instruction after the `WAIT`. -/
def LowPowerTime (i : Impl) (a : Arch) : Arch :=
  if i.WaitRestartsOnNotEnabled && InterruptRequests i a ≠ 0#8 then { a with LowPower := false }
  else a

end Manual

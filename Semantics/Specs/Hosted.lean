import Semantics.Specs.Syscall
import Semantics.Specs.Invariants
import Semantics.Specs.RegFileSize

/-!
# Hosted — the environment layer (`Semantics/Env.lean`), which is NOT the architecture

The hosted run (`hostStep` / `runHosted`) wraps the processor (`step`) with the conventions of
this model's environment: the MARS-style `syscall` services and the stopping conventions. The
theorems here say exactly where the hosted run differs from the bare processor:

* `hostStep_eq_step`: when the run is not stopped and no hosted service is selected, a hosted step
  *is* a processor step (the output buffer unchanged); `runHosted_agrees_with_run` lifts this to
  whole runs (the hosted run then ends in the state of the bare `run`).
* `hostStep_syscall_spec`: what a `syscall` does in the hosted run (the dispatch on `$v0`);
  `hosted_print_int` and `hosted_exit` are the two named cases.
* `hostStep_stop`: the stopping conventions.
* `runHosted_preserves_zero_register`, `runHosted_preserves_wellFormed`: the global invariants
  hold for the hosted run too (the services touch no register).

## Theorems in this file (13)

  `readCStringSpec_eq` `hostStep_stop` `hostStep_eq_step` `hostStep_bare_eq_step`
  `runHosted_go_agrees` `runHosted_agrees_with_run` `hostStep_syscall_spec` `hosted_print_int`
  `hosted_exit` `hostStep_preserves` `runHosted_preserves_zero_register`
  `runHosted_preserves_wellFormed`
  `runHosted_go_preserves`
-/

set_option maxRecDepth 4000

/-- `readCStringSpec` is `Env.lean`'s `readCString` (definitionally: it is an abbreviation, not
a copy). -/
theorem readCStringSpec_eq (s : State) (addr : W32) (fuel : Nat) :
    readCStringSpec s addr fuel = readCString s addr fuel := rfl

/-- **The stopping conventions**: the hosted run stops (and the processor is not stepped) when
`stopReason` applies — `pc` word-aligned and outside the loaded image. -/
theorem hostStep_stop (env : HostEnv) (h : Hosted) (r : HaltReason)
    (hstop : stopReason env h.machine = some r) :
    hostStep env h = .halt r := by
  unfold hostStep; rw [hstop]

/-- **A hosted step is a processor step when no service is selected.** If the stopping convention
does not apply and either services are off or the instruction at `pc` selects no hosted service,
`hostStep` steps the processor and leaves the output buffer alone. -/
theorem hostStep_eq_step (env : HostEnv) (h : Hosted)
    (hstop : stopReason env h.machine = none)
    (hsvc : env.services = false ∨ selectedService h.machine = none) :
    hostStep env h = .next { h with machine := step h.machine } := by
  unfold hostStep
  rw [hstop]
  dsimp only
  rcases hsvc with hs | hs <;> simp [hs]

/-- With services off (the bare mode, `MipsRun --bare`), every hosted step that is not stopped is
a processor step — a `syscall` included. -/
theorem hostStep_bare_eq_step (env : HostEnv) (h : Hosted) (hbare : env.services = false)
    (hstop : stopReason env h.machine = none) :
    hostStep env h = .next { h with machine := step h.machine } :=
  hostStep_eq_step env h hstop (Or.inl hbare)

/-- `runHosted`'s loop agrees with `run` (proof device for `runHosted_agrees_with_run`). -/
theorem runHosted_go_agrees (env : HostEnv) (out : String) (n : Nat) (s : State) (k : Nat)
    (hquiet : ∀ j, j < n → stopReason env (run s j) = none ∧
      (env.services = false ∨ selectedService (run s j) = none)) :
    runHosted.go env n { machine := s, out := out } k
      = .limitReached { machine := run s n, out := out } (k + n) := by
  induction n generalizing s k with
  | zero => rfl
  | succ n ih =>
    obtain ⟨h1, h2⟩ := hquiet 0 (by omega)
    unfold runHosted.go
    rw [hostStep_eq_step env _ h1 h2]
    dsimp only
    rw [ih (step s) (k + 1) (fun j hj => hquiet (j + 1) (by omega))]
    rw [show k + 1 + n = k + (n + 1) by omega]
    rfl

/-- **The hosted run agrees with the bare run whenever no hosted service is selected.** If for
every state the bare `run` passes through in `n` steps the stopping convention does not apply and
no service is selected (or services are off), then `runHosted` runs out of fuel after exactly `n`
steps in the bare run's final state, with the output buffer unchanged. -/
theorem runHosted_agrees_with_run (env : HostEnv) (out : String) (n : Nat) (s : State)
    (hquiet : ∀ j, j < n → stopReason env (run s j) = none ∧
      (env.services = false ∨ selectedService (run s j) = none)) :
    runHosted env n { machine := s, out := out } = .limitReached { machine := run s n, out := out } n := by
  unfold runHosted
  rw [runHosted_go_agrees env out n s 0 hquiet, Nat.zero_add]

/-- **`syscall` in the hosted run (services on)**: dispatch on `$v0` (register 2). Services 1, 4
and 11 append to the output buffer — the signed decimal rendering of `$a0`, the NUL-terminated
string at `$a0` (at most `printStringFuelSpec` bytes), the character whose code is the low byte of
`$a0` — and complete the `syscall` (`pc + 4`, outside a delay slot) changing nothing else in the
processor; service 10 stops the run with `exit`; any other `$v0` is a processor step, i.e. the
System Call exception (`syscall_spec_raw`). -/
theorem hostStep_syscall_spec (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hpb : h.machine.pendingBranch = none) (hexec : executesInstr h.machine = true) :
    hostStep env h =
      match (readReg h.machine (regIdxSpec 2#32)).toNat with
      | 1 => .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
                     out := h.out ++ toString (asSigned (readReg h.machine (regIdxSpec 4#32))) }
      | 4 => .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
                     out := h.out ++ readCStringSpec h.machine (readReg h.machine (regIdxSpec 4#32))
                       printStringFuelSpec }
      | 10 => .halt .exit
      | 11 => .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
                      out := h.out ++ String.singleton
                        (Char.ofNat ((readReg h.machine (regIdxSpec 4#32) &&& 0xff#32).toNat)) }
      | _ => .next { h with machine := timerTick (takeException h.machine excCodeSys) } := by
  obtain ⟨s, out⟩ := h
  simp only at hstop hfetch hpb hexec ⊢
  have h2 : regIdxSpec 2#32 = 2 := by decide
  have h4 : regIdxSpec 4#32 = 4 := by decide
  rw [h2, h4]
  unfold hostStep
  rw [hstop]
  simp only [hon, hexec, Bool.and_self, ↓reduceIte]
  unfold selectedService
  rw [hfetch]
  simp only [hdecode]
  have hadv : advance s s = { s with pc := s.pc + 4#32 } := by unfold advance; rw [hpb]
  have hsys : step s = timerTick (takeException s excCodeSys) := syscall_spec_raw s w code hfetch hdecode hexec
  generalize (readReg s 2).toNat = n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
    simp only [performService, hadv, hsys, readCStringSpec, printStringFuelSpec]

/-- **Hosted service 1 (print int)** appends the signed decimal rendering of `$a0` to the output,
with no trailing newline, and completes the `syscall` (`pc + 4`); the processor state is otherwise
unchanged. (Formerly `syscall1_spec`, a statement about `step`.) -/
theorem hosted_print_int (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 1#32)
    (hpb : h.machine.pendingBranch = none) (hexec : executesInstr h.machine = true) :
    hostStep env h =
      .next { machine := { h.machine with pc := h.machine.pc + 4#32 },
              out := h.out ++ toString (asSigned (readReg h.machine (regIdxSpec 4#32))) } := by
  rw [hostStep_syscall_spec env h w code hstop hon hfetch hdecode hpb hexec, hv0]; rfl

/-- **Hosted service 10 (exit)** stops the run with `exit`, whatever else holds — in or out of a
delay slot. (Formerly `syscall10_spec`, a statement about `step`.) -/
theorem hosted_exit (env : HostEnv) (h : Hosted) (w code : W32)
    (hstop : stopReason env h.machine = none) (hon : env.services = true)
    (hfetch : readMemWord h.machine h.machine.pc = some w)
    (hdecode : decode w = some (.syscall code))
    (hv0 : readReg h.machine (regIdxSpec 2#32) = 10#32) (hexec : executesInstr h.machine = true) :
    hostStep env h = .halt .exit := by
  have h2 : regIdxSpec 2#32 = 2 := by decide
  rw [h2] at hv0
  unfold hostStep
  rw [hstop]
  simp only [hon, hexec, Bool.and_self, ↓reduceIte]
  unfold selectedService
  rw [hfetch]
  simp only [hdecode, hv0]
  rfl

/-- Any property of the processor state that `step` preserves and that completing an instruction
without effect (`advance s s`, what a print service does) preserves, is preserved by a hosted
step (proof device). -/
theorem hostStep_preserves (P : State → Prop) (hstep : ∀ s, P s → P (step s))
    (hadv : ∀ s, P s → P (advance s s)) (env : HostEnv) (h h' : Hosted)
    (hp : P h.machine) (hs : hostStep env h = .next h') : P h'.machine := by
  unfold hostStep at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i svc _
      cases svc <;> simp only [performService] at hs <;>
        first | (cases hs; exact hadv _ hp) | cases hs
    · cases hs; exact hstep _ hp

/-- The loop of `runHosted` preserves such a property (proof device). -/
theorem runHosted_go_preserves (P : State → Prop) (hstep : ∀ s, P s → P (step s))
    (hadv : ∀ s, P s → P (advance s s)) (env : HostEnv) (n : Nat) (h : Hosted) (k : Nat)
    (hp : P h.machine) : P (runHosted.go env n h k).final.machine := by
  induction n generalizing h k with
  | zero => exact hp
  | succ n ih =>
    unfold runHosted.go
    split
    · exact hp
    · rename_i h' hs
      exact ih h' (k + 1) (hostStep_preserves P hstep hadv env h h' hp hs)

/-- **`$zero` is unchanged by a hosted run**: the hosted services write no register. -/
theorem runHosted_preserves_zero_register (env : HostEnv) (n : Nat) (h : Hosted) :
    readReg (runHosted env n h).final.machine 0 = readReg h.machine 0 :=
  runHosted_go_preserves (fun s => readReg s 0 = readReg h.machine 0)
    (fun s hs => (step_preserves_zero_register s).trans hs)
    (fun s hs => (readReg_zero_of_regs_eq (advance_regs s s)).trans hs) env n h 0 rfl

/-- **A hosted run from a well-formed state ends in a well-formed state** (both register files
of size 32), as the bare run does (`run_preserves_wellFormed`). -/
theorem runHosted_preserves_wellFormed (env : HostEnv) (n : Nat) (h : Hosted)
    (hwf : h.machine.RegFilesWF) : (runHosted env n h).final.machine.RegFilesWF :=
  runHosted_go_preserves State.RegFilesWF (fun s hs => step_preserves_wellFormed s hs)
    (fun s hs => ⟨(advance_regs s s).symm ▸ hs.1, (advance_fpRegs s s).symm ▸ hs.2⟩) env n h 0 hwf

/-! ### Satisfiable examples -/

-- Service 1 prints `$a0` and the run continues; service 10 stops it.
#guard
  let p := buildProgSpec textBase [.syscall 0#32, .syscall 0#32]
  let s := setRegsSpec (load p) [(2, 1#32), (4, 5#32)]
  match hostStep { image := p } { machine := s } with
  | .next h => h.out == "5" && h.machine.pc == textBase + 4#32
  | .halt _ => false

#guard
  let p := prog1Spec (.syscall 0#32)
  let s := setRegsSpec (load p) [(2, 10#32)]
  match hostStep { image := p } { machine := s } with
  | .next _ => false
  | .halt r => r == .exit

-- In the bare mode the same `syscall` is the System Call exception.
#guard
  let p := prog1Spec (.syscall 0#32)
  let s := setRegsSpec (load p) [(2, 1#32), (4, 5#32)]
  match hostStep { image := p, services := false } { machine := s } with
  | .next h => h.out == "" && causeExcCode h.machine == excCodeSys
  | .halt _ => false

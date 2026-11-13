# scripts/ -- the gated flow

Rule: every wave ends with a full gate run; only a fully green gate is committed, locally. One deterministic script enforces it.

| Script | What it does |
|---|---|
| `gate.sh` | Runs the 10 gate steps, prints `[n/10] name ... PASS/FAIL/SKIP (s)`, keeps logs in `.gate/logs/`, always writes `.gate/last-run.json`; on a full green run writes the stamp `.gate/green` (tree id of the exact verified content, timestamp, HEAD, toolchain, per-step results). |
| `gate-commit.sh "<subject>" [body-file]` | Commits only if on a non-main branch, the stamp exists, and the current tree id equals the stamp. Stages `git add -A`, re-verifies the staged tree, commits with a `Gate:` trailer block and `Co-Authored-By` last. Never pushes. `--run` runs the gate first. |
| `install-hooks.sh` | `git config core.hooksPath .githooks` for this clone (idempotent). The `pre-commit` hook then blocks any commit whose staged tree differs from the stamp. Bypass in an emergency: `git commit --no-verify`. |
| `trace.py` | Generates `docs/TRACE.md` (`--check`: exit 1 on missing step arm / spec theorem / sorry; `--out FILE`; `--json FILE`). Also owns the generated coverage table in the root `README.md` (between `<!-- BEGIN GENERATED: trace.py --readme -->` and `<!-- END GENERATED -->`): `--readme` prints it, `--write-readme` rewrites the block, `--check-readme` exits 1 if the block differs from fresh output and writes nothing; a plain run that writes `docs/TRACE.md` (so `gate.sh --fix`) refreshes the block too. The test data scans `tests/corpus`, `tests/equiv`, `tests/asm` and `tests/oracle` (`oracle` is a separate column). |
| `gate-allow.txt` | Optional, absent by default. Lines `path:construct  # reason` allow a forbidden construct in one file. A line without a reason is an error. |

## Steps

| # | name | PASS when |
|---|---|---|
| 1 | forbidden | no `sorry admit native_decide bv_decide axiom partial def unsafe @[implemented_by @[extern` in CODE of `Semantics/**`, `Checked/Semantics/DiffHarness/EquivHarness/MipsRun.lean` (comments, docstrings, strings stripped first; `gate.sh --selftest` shows the stripper's cases) |
| 2 | build | `lake build Semantics Checked DiffHarness EquivHarness MipsRun` exits 0 and has 0 compiler warnings from project files (`--allow-warnings` relaxes) |
| 3 | check | `lake check` exits 0 and its `Uses axioms:` line is a subset of propext, Classical.choice, Quot.sound (missing line = FAIL) |
| 4 | comparator | `lake comparator` exits 0 and prints `Your solution is okay!` |
| 5 | diffharness | `lake exe DiffHarness` exits 0, and `SUMMARY: all N corpus programs PASS` has N = number of `tests/corpus/*.asm`; java and `vendor/mars/Mars4_5.jar` required (missing = FAIL) |
| 6 | equivharness | `lake exe EquivHarness` exits 0 with `SUMMARY: all N equivalence cases behaved as claimed` |
| 7 | oracle | `scripts/oracle.py selftest`, then `oracle.py --asm` (QEMU 24Kf vs the model on `tests/oracle/*.asm` + the runnable `tests/asm/*.asm`) and `oracle.py --encodings` (our assembler vs llvm-mc) all exit 0: no undeclared mismatch, no stale declaration, no harness error; prints counts (tests / pass / declared QEMU deviations / known model bugs / skipped, encodings same / declared). `qemu-system-mips` or the LLVM tools missing = FAIL (exit 2), never a skip. Not in `--quick` |
| 8 | trace | `trace.py --check` passes, regenerating TRACE.md matches the committed one (ignoring the `- git HEAD:` line), and `trace.py --check-readme` passes (the README's generated coverage table is current); `--fix` rewrites both. The TRACE.md comparison needs the manual texts (its manual column), so it fails on a machine that has not run `docs/spec/manuals/fetch.sh` |
| 9 | manuals | `mipsdoc.py selftest` passes; SKIP (not PASS) if the manual texts are absent |
| 10 | hygiene | no conflict markers, no file >5 MB, no pdf to be committed; `git diff --check` is a warning only |

Flags: `--quick` (1,8,9,10 only; NOT green, no stamp), `--from STEP`, `--only STEP` (number, letter a-j or name), `--allow-warnings`,
`--fix`, `--json` (also print the JSON), `--selftest`. Exit 0 iff no step failed. Env for testing: `GATE_ROOT`, `GATE_DIR`, `GATE_CORPUS_DIR`.
The stamp is written only if the tree id is unchanged between the start and the end of the run.

## Typical flow
```
scripts/gate.sh --quick                 # while iterating: seconds, not a green gate
scripts/gate.sh --fix                   # end of wave: full gate (minutes), regenerates TRACE.md
scripts/gate-commit.sh "Subject line"   # commits exactly the verified tree, locally
# or both at once: scripts/gate-commit.sh --run "Subject line"
```

## CI
`.github/workflows/ci.yml` runs the gate: it installs elan, a JRE, `qemu-system-mips`, `llvm` + `lld` and `poppler-utils`,
sets `ORACLE_LLVM_DIR`, restores the `.lake` cache, runs `lake exe cache get`, tries `docs/spec/manuals/fetch.sh`
(best effort, `continue-on-error`) and then `scripts/gate.sh`, and uploads `.gate/` as an artifact. The manual texts are not
committed. If `fetch.sh` fails, step 9 (manuals) is a SKIP, which does not fail the gate, but step 8 compares
`docs/TRACE.md`, whose manual column needs those texts, so it fails too; CI is therefore only meaningful when the fetch works.
The snippet for the oracle tools:
```yaml
      - name: Install the differential-oracle tools (QEMU MIPS system emulator + LLVM)
        run: |
          sudo apt-get update
          sudo apt-get install -y qemu-system-mips llvm lld poppler-utils
          echo "ORACLE_LLVM_DIR=$(dirname "$(readlink -f "$(command -v llvm-mc || ls /usr/lib/llvm-*/bin/llvm-mc | tail -1)")")" >> "$GITHUB_ENV"
```
(`oracle.py` looks in `$ORACLE_LLVM_DIR`, then `/usr/lib/llvm-21/bin`, then `PATH`; `ld.lld` and `llvm-objcopy` must sit next to `llvm-mc`; on Debian/Ubuntu they do under `/usr/lib/llvm-N/bin`.)
The stamp written in CI is irrelevant; the exit code is the verdict. The workflow has not been run by its author (no CI access from the authoring environment).

## Troubleshooting
- "stale stamp" / hook blocks: something changed after the gate (even a whitespace edit or a regenerated TRACE.md). Re-run `scripts/gate.sh`.
- "tree changed while the gate ran": another agent or editor wrote files during the run; re-run when the tree is quiet.
- java missing / `Mars4_5.jar` missing: step 5 FAILs by design. Install a JRE; the jar lives in `vendor/mars/`.
- Lock contention ("waiting for lock", hangs): another `lake` is running in the same tree. Wait, or gate from your own worktree
  (`git worktree add`, copy `.lake` in). `lake check` alone takes 2-5 min.
- TRACE.md stale: `python3 scripts/trace.py` (or `gate.sh --fix`) and include it in the commit.
- manuals SKIP: run `docs/spec/manuals/fetch.sh` (needs `pdftotext`); a SKIP does not block the stamp but is recorded in the commit trailer.
- Reading failures: logs are `.gate/logs/NN-name.log`; `.gate/` is gitignored.


## Differential oracle: QEMU vs the model (`oracle.py`)

A second oracle next to MARS. It runs **the same machine code at the same addresses** on `qemu-system-mips` (`-M malta -cpu 24Kf`,
big-endian MIPS32r2, legacy-NaN FPU) and on the Lean model, then compares the final architectural state. Unlike MARS it handles
rotr/rotrv/seb/seh/wsbh/ext/ins, branch-likely, sync/synci, cfc1/ctc1, lwl/lwr/swl/swr (big-endian) and delay-slot/exception semantics.

```
python3 scripts/oracle.py                 # all tests/oracle/*.asm; exit 1 iff any FAIL
python3 scripts/oracle.py --only NAME     # repeatable; -v shows details of passing tests too
python3 scripts/oracle.py --list          # tests + their `# oracle:` directives
python3 scripts/oracle.py --json out.json --keep   # --keep leaves ELF/ld script/image sources in a temp dir
python3 scripts/oracle.py --asm           # also the runnable tests/asm programs (the others are listed as SKIP with the reason)
python3 scripts/oracle.py --encodings     # assembler oracle: our Asm.lean vs llvm-mc (-triple=mips-unknown-elf -mcpu=mips32r2)
python3 scripts/oracle.py selftest        # checks the harness itself (judge logic + end-to-end FAIL/DEVIATION behaviour)
```
Needs `qemu-system-mips`, LLVM tools (`llvm-mc ld.lld llvm-objdump llvm-objcopy`; `/usr/lib/llvm-21/bin` or `ORACLE_LLVM_DIR`),
`lake` (it runs `lake build MipsRun`; `ORACLE_NO_BUILD=1` skips that) and Python 3 stdlib. A missing tool exits 2 with a message; nothing is
silently skipped. Output: one line per test `PASS` / `FAIL` / `DEVIATION(declared)`, then
`SUMMARY: N tests, P pass, D declared deviations, K known model bugs, F fail, S skipped`. A few seconds for all tests (parallel), ~60 ms of QEMU per test.

Many of the tests (FP compare/convert/flag/trap/CpU/random-pool programs) are produced by `tests/oracle/gen/gen_tests.py` (deterministic; the committed `.asm` files are the artefacts).

### How a test runs
1. `lake exe MipsRun --max-steps N prog.asm` (our assembler, our model) prints one JSON object. Besides the original fields it carries the
   oracle extension: `image` (`[addr, word]` for every assembled word: text 0x00400000, data 0x10010000, `.ktext` 0x80000180),
   `initial`/`final` (pc, gpr[32], hi, lo, fpr[32] raw bits, fcsr, fp_cond_flag (= FCSR bit 23, kept for compatibility), ll_bit, ll_addr, pending_branch, cp0{status,cause (as `mfc0` reads it: with `TI`/`IP7`),epc,badvaddr,errorepc,ebase,count,compare,hwrena}),
   `halt` (`kind` = exit | unhandled_exception{code,epc,badvaddr} | no_instruction{pc} | limit), `fcsr_mask` (= 0xFF83FFFF: every FCSR bit the model implements; bits 22..18 are reserved and read zero), `memory`
   (every nonzero aligned word of the final **physical** memory, keyed by its **virtual** address `Env.canonicalVAddr`: the model has the Fixed
   Mapping MMU, so the loaded data at virtual 0x10010000 lives at physical 0x50010000 and is reported as 0x10010000) and `physical_memory`
   (the same words by physical address). The oracle compares `memory` with QEMU's memory read back **by virtual address** (in Kernel Mode,
   through the harness's TLB), so both sides speak virtual addresses; `image` is virtual too.
2. `oracle.py` builds a per-test ELF: the fixed harness `tests/oracle/harness/boot.s` + a generated image (config words, the program image
   at kseg0 aliases of RAM pages, TLB entry table) linked by a generated linker script with one PT_LOAD per section.
3. QEMU boots it (`-kernel`, reset entry in kseg0). The stub programs 16 TLB entries (4 KB pages, PageMask 0): text pages (+ the odd partner
   of an even last page), data 0x10010000..+32 KB, stack 0x7fffe000..+8 KB, page 0 (harness scratch at 0xE00..0xFFF, do not use). It then loads
   **all initial values from the model's `initial` JSON** (GPRs, HI/LO, FPRs, FCSR, Status, Cause, EPC, ErrorEPC; `$sp` = `spInit`, `$gp` = 0)
   and jumps to the model's start pc with `$k0 = $k1 = 0`. Status is exactly the model's initial value (0x20000000: CU1 set, so the FPU works and the raw Status read agrees).
4. Exceptions go to 0x80000180: the test's own `.ktext` if it has one, else the harness default handler. The default handler
   * emulates the model's environment calls `$v0` = 1 (print int), 4 (print string), 11 (print char) into an output buffer and resumes after the
     syscall (EPC+4; in a delay slot (Cause.BD = 1) it decodes the branch at EPC (j/jal/jr/jalr/beq/bne/blez/bgtz/regimm incl. likely forms/bc1t/bc1f) and resumes at its target);
     all registers, HI/LO, $k0/$k1 are preserved;
   * `$v0 = 10` (exit): dumps state, `pc` = the syscall address, Status.EXL and Cause.BD/ExcCode hidden (they belong to the harness's syscall exception);
   * any other exception: dumps state as is (`$k0/$k1` restored), `pc` reported as 0x80000180, compared with the model's `unhandledException`.
   A TLB refill (vector 0x80000000, owned by the harness even with `.ktext`) means the guest ran into an unmapped page: a fetch (EPC = BadVAddr) is the
   counterpart of the model's `no_instruction` (running off the text end, jr to nowhere); a data access to an unmapped page is a harness error (the test touched memory the harness does not map).
5. The dump (GPRs, HI/LO, FCSR, Status/Cause/EPC/BadVAddr/ErrorEPC, pc, FPRs, syscall output, every nonzero word of the data+stack pages) goes out
   over the Malta UART as hex; the stub writes Malta SOFTRES and QEMU exits (`-no-reboot`). Hang guard: a wall-clock timeout (`--timeout`, default 20 s);
   QEMU has no instruction budget in this setup, the model side is bounded by `--max-steps` (directive `# oracle: max-steps N`, default 100000).

Tests **with** a `.ktext` handler cannot use the environment syscalls (they would be exceptions for the handler on QEMU): end them by running off the
end of the text (the model reports `no_instruction`, QEMU a TLB refill; both count as the same termination).

### What is compared (and what is masked, with reasons)
GPRs (all 32; **nothing** is ignored by default: the harness preserves $k0/$k1), HI, LO, FPRs (raw 32-bit), FCSR under the model's `fcsr_mask`,
Status & `0x3040ff17` (IE, EXL, ERL, UM, IM7..0, BEV, CU0, CU1), Cause & `0xb880037c` (BD, CE, DC, IV, IP1..0, ExcCode; QEMU's TI, IP7..IP2, WP, PCI are hardware state the model lacks),
EPC, BadVAddr, ErrorEPC, pc, syscall output, final data+stack memory (virtual addresses on both sides, see step 1), termination kind (+ ExcCode for exceptions).
Address translation: the model's MMU is the Fixed Mapping MMU (kuseg = virtual + 0x4000_0000 while ERL = 0), QEMU 24Kf's kuseg is TLB-mapped by the
harness; neither physical placement is observable by a test that uses virtual addresses, so the kuseg offset is checked on the model only
(`Semantics/Specs/Mmu.lean`, `Loader.lean`). kseg0/kseg1 aliasing, the ERL = 1 kuseg identity map and User-Mode Address Errors are deterministic
on both and are compared (`tests/oracle/mmu_*`). A test that sets ERL = 1 runs that code from kseg0 (`.ktext`): executing from kuseg with ERL = 1 is
UNDEFINED (MD00090 Vol III Rev 6.02 A.1.2 p.316) and QEMU would fetch from physical = virtual.
Skipped by termination kind: for `no_instruction` the Status/Cause/EPC/BadVAddr/pc (QEMU's describe its TLB refill); for `exit` the EPC (QEMU's syscall exception clobbers it).
Not observable on QEMU: the LL bit (reported by MipsRun, not compared; `ll_sc_*` tests observe it through `sc`).

### Per-test directives (comment lines `# oracle: ...`)
| directive | meaning |
|---|---|
| `ignore-regs k0 k1 ...` | do not compare these GPRs |
| `unpredictable <field> <citation>` | UNPREDICTABLE per the manual: field not compared (citation mandatory) |
| `expect-deviation <field> <reason + manual citation>` | the MANUAL and QEMU disagree (manual wins): the mismatch is reported as `DEVIATION(declared)`; an **undeclared** mismatch FAILs; a declaration that does **not** occur FAILs (stale) |
| `known-model-bug <field> <manual citation> <one-line description>` | the MODEL is wrong per the manual: reported as `KNOWN-MODEL-BUG`, counted separately, does not fail; FAILs when the mismatch stops occurring |
| `expect <field>=<value> ...` | assertion on the MODEL's value taken from the manual (a failing model is reported as `model != manual expectation`) |
| `max-steps N` | model step budget |
| `bare` | run the model with `MipsRun --bare` (no hosted syscall services); requires a `.ktext` handler, which then services every exception |
Fields: `gpr:t0` (or `gpr`), `fpr:f4` (or `fpr`), `hi lo fcsr status cause epc badvaddr errorepc pc output term`, `mem:0x10010004` (or `mem`).

### Encoding oracle (`--encodings`)
`tests/oracle/encodings.list` (generated once from the `rTable/iTable/bTable/cop1Table` of `Semantics/Asm.lean`, then hand-extended) has one form per line,
`@T` / `@B` = label ahead / behind. Each form is assembled in a 64-byte-aligned slot by our assembler (via MipsRun's image) and by llvm-mc
(+ `.set noreorder`/`.set noat` only in the llvm copy; `div rs,rt` is spelled `div $zero,rs,rt` there) and the words are compared; mismatches print both encodings and llvm-objdump's disassembly.
Every mnemonic of the Asm.lean tables **and** of every `Instruction` constructor (`trace.py --json`) must be in the list. Known, intended differences are in `ENC_DECLARED` in
`oracle.py` (our `li`/`la`/`move`/`abs` expansions follow MARS/SPIM); a declaration that no longer occurs FAILs.

### In the gate
Step 7 of `gate.sh` runs `oracle.py selftest`, `oracle.py --asm` and `oracle.py --encodings` and FAILs on any undeclared mismatch, stale declaration, harness error or missing tool.
It prints `N tests: P pass, D declared QEMU deviations, K known model bugs, S skipped; encodings X same, Y declared`.

### Model-bug triage (`known-model-bug`)
`# oracle: known-model-bug <field> <manual citation> <one-line description>` marks a mismatch where the MODEL is wrong per the manual and is not fixed yet (the gate cannot be red for it, but it must stay visible).
It is reported in its own section (`KNOWN-MODEL-BUG`), counted separately in the SUMMARY, does not fail the run, and FAILs if the mismatch stops occurring (so the directive must be deleted when the bug is fixed). Zero exist today.

### Programs of `tests/asm`
`--asm` also runs the `tests/asm/*.asm` programs (names `asm/NAME`), using sidecar directives kept in `oracle.py` (`ASM_DIRECTIVES`; the programs are not edited because EquivHarness reads them).
Programs the harness cannot judge are listed as `SKIP name: reason` and counted (`ASM_SKIP` plus an automatic rule: a `.ktext` handler containing `syscall`, and EBase relocation `mtc0 $x,$15,1`).

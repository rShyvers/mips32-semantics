---
name: mips-manual
description: Look up MIPS32 architecture facts in the vendored manuals with mipsdoc.py and cite them correctly. Use whenever you need to state, verify or implement what the manual says about an instruction, register, exception or FP behaviour.
---

# /mips-manual -- look it up, never recall it

Tool: `python3 manuals/mipsdoc.py` (stdlib only). First run `... selftest`; if it prints SKIP the texts are absent:
run `manuals/fetch.sh` (needs `pdftotext`). Details: `manuals/AGENTS.md`. Do not read the 20k-line `.txt` files.

## Subcommands (pick by what you know)
- Instruction known: `insn NAME` (assembler spellings ok: `c.eq.s`, `jr.hb`); `--rev 2.50` for the Release 2 manual.
- Section/register known: `section DOC "Cause Register"` or `section v3 9.36`; browse with `toc DOC REGEX`; `list REGEX`.
- Concept only: `search "words" [-d v3] [-k 5] [--full]`, then `section`/`page` on the hit.
- Every mention of a token: `grep REGEX -d v1`. A page by printed number: `page v2 177 -n 2`. Citation line: `cite v3 87`.
- IEEE 754: `ieee` = IEEE Std 754-2019 (licensed, LOCAL-ONLY, see `manuals/LOCAL-SOURCES.md`; works if
  `IEEE-754-2019.txt` is installed): `section ieee 6.3`, `search -d ieee "..."`, `page ieee 50`, `cite ieee 50`. `p754` = the
  public 2006 draft. Never quote more than a sentence or two of 754; never commit or upload the PDF/text.
- Documents: `v1` Vol I-A 6.01, `v2` Vol II-A 6.06, `v3` Vol III 6.02 (latest, normative); `v2old`/`v3old` Rev 2.50; `v1r3`, `v1r0`.

## Reading rule (this project's target)
MIPS32 Release 6 (CLAUDE.md, "Target profile"): little-endian, 64-bit FPU (`Status.FR=1`), IEEE 754-2008 NaNs
(`FIR.Has2008=1`), Fixed Mapping MMU, no optional modules. Read the Release 6 wording;
instructions marked "removed in Release 6" (branch-likely, HI/LO, LWL/LWR, C.cond.fmt, ...) are not in the model. Where a
lookup shows a legacy and an R6 page (DIV vs DIV MOD DIVU MODU), the R6 page applies. Rev 2.50 is only for the Release 2
model kept at tag `mips32r2-final`.

## Citation format
Document number + revision + instruction or section + PRINTED page, e.g.
`MD00086 Vol II-A Rev 6.06, ERET, p.177` or `MD00090 Vol III Rev 6.02, 6.2.3 General Exception Processing, p.86`.
IEEE: `IEEE Std 754-2019 §6.3, p.50` (clause + printed page; say "verified against 754-2019", the MIPS manual names 754-1985).
The heading `== <doc> p.<printed> (pdf page N) ==` printed by the tool gives the parts; `cite DOC PAGE` prints it for you.
Never cite the pdf page, never cite from memory, never cite a page you did not open this session.

## Pages with no extracted text
Some instruction pages are image-only: `insn` says so and prints the PDF page. Read that page with the Read tool on the PDF:
`Read file_path=manuals/<file>.pdf pages="N"` using the pdf page number mipsdoc printed (max 20 pages per call).
Cite it with the printed page found on the image. If the PDF is absent, say the claim is unverified; do not guess.

## Output discipline
Quote the exact pseudocode/wording you rely on, state which statement of the model it supports or contradicts, and mark
anything you could not find as "not found in <doc> (searched: ...)".

---
name: mips-manual
description: Look up MIPS32 architecture facts in the vendored manuals with mipsdoc.py and cite them correctly. Use whenever you need to state, verify or implement what the manual says about an instruction, register, exception or FP behaviour.
---

# /mips-manual -- look it up, never recall it

Tool: `python3 docs/spec/manuals/mipsdoc.py` (stdlib only). First run `... selftest`; if it prints SKIP the texts are absent:
run `docs/spec/manuals/fetch.sh` (needs `pdftotext`). Details: `docs/spec/manuals/AGENTS.md`. Do not read the 20k-line `.txt` files.

## Subcommands (pick by what you know)
- Instruction known: `insn NAME` (assembler spellings ok: `c.eq.s`, `jr.hb`); `--rev 2.50` for the Release 2 manual.
- Section/register known: `section DOC "Cause Register"` or `section v3 9.36`; browse with `toc DOC REGEX`; `list REGEX`.
- Concept only: `search "words" [-d v3] [-k 5] [--full]`, then `section`/`page` on the hit.
- Every mention of a token: `grep REGEX -d v1`. A page by printed number: `page v2 177 -n 2`. Citation line: `cite v3 87`.
- Documents: `v1` Vol I-A 6.01, `v2` Vol II-A 6.06, `v3` Vol III 6.02 (latest, normative); `v2old`/`v3old` Rev 2.50; `v1r3`, `v1r0`.

## Reading rule (this project's target)
Pre-Release-6 MIPS32, Release 2 feature set, big-endian, legacy FP (`FIR.Has2008=0`). Read the "Pre-Release 6" wording;
ignore R6-only instructions (BALC, ALUIPC, CMP.cond.fmt, MADDF, SELEQZ...) and R6-only register text. Where a lookup shows a
legacy and an R6 page (DIV vs DIV MOD DIVU MODU), the plain name is the legacy one. Latest revisions win over Rev 2.50
unless the claim is explicitly about Release 2 numbering.

## Citation format
Document number + revision + instruction or section + PRINTED page, e.g.
`MD00086 Vol II-A Rev 6.06, ERET, p.177` or `MD00090 Vol III Rev 6.02, 6.2.3 General Exception Processing, p.86`.
The heading `== <doc> p.<printed> (pdf page N) ==` printed by the tool gives the parts; `cite DOC PAGE` prints it for you.
Never cite the pdf page, never cite from memory, never cite a page you did not open this session.

## Pages with no extracted text
Some instruction pages are image-only: `insn` says so and prints the PDF page. Read that page with the Read tool on the PDF:
`Read file_path=docs/spec/manuals/<file>.pdf pages="N"` using the pdf page number mipsdoc printed (max 20 pages per call).
Cite it with the printed page found on the image. If the PDF is absent, say the claim is unverified; do not guess.

## Output discipline
Quote the exact pseudocode/wording you rely on, state which statement of the model it supports or contradicts, and mark
anything you could not find as "not found in <doc> (searched: ...)".

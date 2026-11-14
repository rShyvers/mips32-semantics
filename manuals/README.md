# MIPS32 architecture manuals (primary sources)

The specification in `docs/spec/` and the semantics in `Semantics/` are checked
against these documents. Run `./fetch.sh` to download them; it verifies
`SHA256SUMS` and, if `pdftotext` is installed, writes a searchable `.txt` next
to each PDF.

**Normative (latest published revisions).** These are the most recent
revisions MIPS published. They still document every pre-Release-6 instruction
(delay-slot branches, branch-likely, HI/LO, `lwl`/`lwr`, ...), each marked
"removed in Release 6", and state configuration-dependent behaviour
explicitly (for example `FIR.Has2008` / `FCSR.ABS2008` / `FCSR.NAN2008`).

| File | Document | Revision |
|---|---|---|
| `MD00086-2B-MIPS32BIS-AFP-06.06.pdf` | Vol II-A: The MIPS32 Instruction Set Manual (MD00086) | 6.06, December 15 2016 |
| `MD00090-2B-MIPS32PRA-AFP-06.02.pdf` | Vol III: MIPS32 / microMIPS32 Privileged Resource Architecture (MD00090) | 6.02, July 10 2015 |
| `MD00082-2B-MIPS32INT-AFP-06.01.pdf` | Vol I-A: Introduction to the MIPS32 Architecture (MD00082) | 6.01, August 20 2014 |

**Historical (the Release 2 baseline the project's docs cite by page).**

| File | Document | Revision |
|---|---|---|
| `MD00086-2B-MIPS32BIS-AFP-02.50.pdf` | Vol II: The MIPS32 Instruction Set (MD00086) | 2.50, July 1 2005 |
| `MD00090-2B-MIPS32PRA-AFP-02.50.pdf` | Vol III: The MIPS32 Privileged Resource Architecture (MD00090) | 2.50, July 1 2005 |
| `MD00082-2B-MIPS32INT-AFP-03.02.pdf` | Vol I-A: Introduction to the MIPS32 Architecture (MD00082) | 3.02, March 21 2011 (Rev 2.50 of Vol I was not found online) |
| `MD00082-2B-MIPS32INT-AFP-00.95.pdf` | Vol I: Introduction to the MIPS32 Architecture (MD00082) | 0.95, March 12 2001 |

**IEEE P754 draft (reference, not a MIPS document).**

| File | Document | Revision |
|---|---|---|
| `IEEE-P754-D1.2.5-2006-10-04.pdf` | DRAFT Standard for Floating-Point Arithmetic P754 (IEEE working group) | Draft 1.2.5, October 4 2006, 59 pages |

This is the public working-group draft of what became IEEE 754-2008, posted on the P754 group's site and
fetched from the Internet Archive copy of it (URL in `fetch.sh`). It is **not** the published standard: that
is sold by IEEE and is not vendored. The MIPS manual (MD00082) names IEEE 754 as its standard, so the draft
is used to check what the manuals defer to IEEE (for example the sign of an exact-zero result, §8.3 p.44).
`mipsdoc.py` key `p754`; cite as `IEEE P754 Draft 1.2.5 (2006-10-04) §8.3 p.44` and say it is a draft.

The PDFs and extracted text are deliberately **not committed** (`.gitignore`):
they are copyright MIPS Technologies, Inc. (the IEEE draft: IEEE, "unapproved draft"), and their front
matter prohibits copying without written permission. The download locations in `fetch.sh` are
university course mirrors, not official MIPS downloads.

**Looking things up.** Do not read the extracted `.txt` files whole: use
`./mipsdoc.py` (stdlib-only Python 3: `insn`, `section`, `search`, `grep`,
`page`, `cite`; `./mipsdoc.py selftest` verifies it). `AGENTS.md` is the short
usage guide, including which revision is normative and how to cite.

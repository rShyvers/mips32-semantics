# Using the MIPS32 manuals (agents and humans)

Do not read the 20k-line `.txt` files. Use `./mipsdoc.py` (Python 3 stdlib only);
it returns exactly the page(s) or section you ask for, each headed with
`== <document> p.<printed page> (pdf page N) ==`. The PDFs and `.txt` are not
committed: run `./fetch.sh` first (needs `pdftotext`); `./mipsdoc.py selftest`
checks the setup and the tool (and skips cleanly if the `.txt` files are absent).

## Which subcommand
- You know the instruction: `insn NAME` (assembler spellings work: `c.eq.s`, `cvt.d.w`, `jr.hb`).
- You know the register / section number or title: `section DOC QUERY` (`toc DOC REGEX` to browse).
- You only know the concept: `search "words" [-d v3]`, then `section` / `page` on the hit.
- You need every mention of a token: `grep REGEX -d v1`. A citation line: `cite DOC PAGE`.

## Examples
```
./mipsdoc.py insn ERET                  # ERET pages (Vol II 6.06), incl. LLbit pseudocode
./mipsdoc.py insn c.eq.s                # all 4 pages of C.cond.fmt
./mipsdoc.py insn mtc0 --rev 2.50       # same lookup in the Release 2 manual (Rev 2.50)
./mipsdoc.py list 'BC1|CVT'             # instruction pages, mnemonic, title, printed pages
./mipsdoc.py section v3 6.2.3           # General Exception Processing incl. pseudocode
./mipsdoc.py section v3 "Cause Register"  # Vol III 9.36 (exact number, or best title match)
./mipsdoc.py section v1 FCSR            # FCSR layout, field table, rounding modes (Vol I 6.5.4)
./mipsdoc.py search "value stored in EPC branch delay slot"   # ranked pages, 3-4 hit lines each
./mipsdoc.py search "unaligned load LWL big endian" -d v2 -k 3 --full   # whole pages
./mipsdoc.py page v3 87 -n 2            # printed pages 87-88;  cite v3 87 -> citation line
```
Documents: `v1` Vol I-A 6.01, `v2` Vol II-A 6.06, `v3` Vol III 6.02 (latest);
historical `v2old`/`v3old` (Rev 2.50), `v1r3` (3.02), `v1r0` (0.95).

## Which revision to trust
The latest revisions (v1/v2/v3) are normative. The model targets a pre-Release-6
MIPS32 processor with the Release 2 feature set and legacy FP (`FIR.Has2008=0`).
So read the "Pre-Release 6" wording (pages are marked "removed in Release 6"
for delay-slot branches, branch-likely, HI/LO, `lwl`/`lwr`, ...) and ignore
Release 6-only instructions (`BALC`, `ALUIPC`, `CMP.cond.fmt`, `MADDF`, `SELEQZ`,
...) and R6-only register text. Where `insn X` shows both a legacy and an R6
page (`DIV` vs `DIV MOD DIVU MODU`), the plain name is the legacy one. Rev 2.50
is the Release 2 baseline the project docs cite by page; use `--rev 2.50`
when a citation must match it.

## Citing
Give document number, revision, instruction or section name, and printed page
(not the PDF page), e.g. `MD00090 Vol III Rev 6.02, 6.2.3 General Exception
Processing, p.86` or `MD00086 Vol II-A Rev 6.06, ERET, p.177`. `cite DOC PAGE`
prints the document/revision/page part.

## Known limits
- Some instruction pages have no extracted text (image-only in the PDF);
  `insn` says so and gives the page to read in the PDF.
- A few headings are missing from the text extraction (e.g. Vol I 6.5); such
  a section is located by its TOC page and starts at the top of that page.
- Section/page numbers are the printed ones; the pdf page is also shown.

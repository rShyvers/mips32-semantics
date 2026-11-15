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
`p754` is the IEEE P754 working-group public DRAFT 1.2.5 (2006-10-04), the draft of what became
IEEE 754-2008 (see "IEEE P754 draft" below); `section`/`toc`/`search -d p754`/`grep -d p754`/`page`/`cite`
work on it, `insn` does not.

`ieee` is IEEE Std 754-2019, the published standard (licensed, LOCAL-ONLY: copyrighted, supplied by the owner, not
fetchable; see `LOCAL-SOURCES.md`). `section ieee 6.3`, `toc ieee`, `search -d ieee`, `grep -d ieee`, `page ieee N`,
`cite ieee N` work on it (clause numbers as in the standard; `insn` does not). If `IEEE-754-2019.txt` is absent the
tool says so and the selftest still passes; then a claim about 754-2019 is unverified here, say so.

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

## IEEE Std 754-2019 (`ieee`)
Headings look like `6.3 The sign bit`; printed page = the bare number above "Copyright (c) 2019 IEEE".
```
./mipsdoc.py section ieee 6.3              # p.50: signs of NaN, products, exact-zero sums, squareRoot(-0)
./mipsdoc.py section ieee "NaN propagation"  # 6.2.3, p.49
./mipsdoc.py search "tininess after rounding" -d ieee    # 7.5, p.53
./mipsdoc.py cite ieee 50
```
Cite as `IEEE Std 754-2019 §6.3, p.50`. Quote at most a sentence or two (the standard is copyrighted). Never copy the
PDF or text anywhere that is committed or uploaded. The MIPS manual names 754-1985; only claim "verified against
754-2019", not that the rule is unchanged since 1985.

## IEEE P754 draft (`p754`)
A public working-group DRAFT (Draft 1.2.5, October 4 2006, 59 pages), not the published IEEE 754. The MIPS
manual (MD00082 Vol I-A Rev 6.01 §6.2, p.77, footnote 1) names IEEE 754 as its standard; the published
standard is sold by IEEE and is not vendored. Use the draft only to check what the manuals defer to IEEE,
and say it is a draft when citing. Headings look like `8.3 The sign bit`; printed page = footer "Page N".
```
./mipsdoc.py section p754 "The sign bit"   # 8.3, p.44: zero-sum signs, product sign, squareRoot(-0)
./mipsdoc.py search "exact zero sum" -d p754
./mipsdoc.py cite p754 44
```
Cite as `IEEE P754 Draft 1.2.5 (2006-10-04) §8.3 p.44`.

## Text-extraction glyph loss
`pdftotext` can lose math glyphs such as "≠" and "<" in tables (for example Vol III Table 6.1 p.73 prints
`IntCtlVS ≠ 0` in its "Not Allowed" row, which the text extraction shows as `0`; that produced a false "the manual
contradicts itself" claim). Before declaring a manual contradiction, render the page and look at it:
`pdftoppm -r 90 -f PDFPAGE -l PDFPAGE -png FILE.pdf OUTPREFIX`.

## Known limits
- Some instruction pages have no extracted text (image-only in the PDF);
  `insn` says so and gives the page to read in the PDF.
- A few headings are missing from the text extraction (e.g. Vol I 6.5); such
  a section is located by its TOC page and starts at the top of that page.
- Section/page numbers are the printed ones; the pdf page is also shown.

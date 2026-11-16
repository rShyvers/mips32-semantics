# LOCAL-ONLY sources (copyrighted, not fetchable, never committed)

These documents are used for verification but are not downloadable from a public mirror. The repo owner supplies
them. The files are ignored by git (`/manuals/*.pdf`, `*.txt` in `/.gitignore`); never `git add`, upload or
quote them at length. Short quotes (a sentence or two) in citations are fine, as for the MIPS manuals.

| File | Document | Revision | SHA-256 of the PDF |
|---|---|---|---|
| `IEEE-754-2019.pdf` | IEEE Std 754-2019, IEEE Standard for Floating-Point Arithmetic (revision of IEEE Std 754-2008), IEEE Computer Society, approved 13 June 2019, published 22 July 2019, 84 pages | 2019 | `2fe5f245fa6fd027a64067e2d91d9000f51e9c61ad23fe1914d8cae41f2b0fb4` |

The PDF is the owner's licensed copy of the published standard, unlike the public working-group draft `p754` that
`fetch.sh` downloads.

## Install

1. Copy the licensed PDF to `manuals/IEEE-754-2019.pdf` and check `sha256sum IEEE-754-2019.pdf` against the
   table (a different hash means a different file or edition: the page numbers in citations may not match).
2. Extract the text exactly as `fetch.sh` does for the MIPS manuals:
   `pdftotext -layout IEEE-754-2019.pdf IEEE-754-2019.txt`, then drop the per-page license-stamp footer lines
   (`sed -i '/Authorized licensed use limited to/d' IEEE-754-2019.txt`); `fetch.sh` does both when the PDF is present.
3. `python3 mipsdoc.py selftest` then runs the extra `ieee` checks. Without the files the selftest only prints a note
   and still passes (the gate's manuals step is unaffected).

## Use

`mipsdoc.py section ieee 6.3`, `search -d ieee "..."`, `grep -d ieee REGEX`, `page ieee 50`, `cite ieee 50`, `toc ieee`.
Printed page numbers are the standard's own (the number above "Copyright (c) 2019 IEEE"; the pdf page is also shown).
Cite as `IEEE Std 754-2019 §6.3, p.50`. Without the file, a claim that cites it is unverifiable here: say so.

#!/bin/sh
# Fetches the MIPS32 architecture manuals this project's spec is checked against.
# The PDFs are copyrighted by MIPS Technologies and are NOT committed (see README.md here).
set -eu
cd "$(dirname "$0")"
UA="Mozilla/5.0 (X11; Linux x86_64) generic-client"
get() { [ -f "$1" ] || curl -sSL -A "$UA" --max-time 300 -o "$1" "$2"; }
get MD00086-2B-MIPS32BIS-AFP-06.06.pdf "https://www.ece.lsu.edu/ee4720/doc/mips32-r6-2a.pdf"
get MD00090-2B-MIPS32PRA-AFP-06.02.pdf "https://www.ece.lsu.edu/ee4720/doc/mips32-r6-3.pdf"
get MD00082-2B-MIPS32INT-AFP-06.01.pdf "https://www.ece.lsu.edu/ee4720/doc/mips32-r6-1a.pdf"
get MD00086-2B-MIPS32BIS-AFP-02.50.pdf "https://faculty.kfupm.edu.sa/coe/mudawar/coe233/tools/MIPS32Vol2.InstructionSet.pdf"
get MD00090-2B-MIPS32PRA-AFP-02.50.pdf "https://vie.engineering.iastate.edu/courses/cpre381x_s06/lectures/MIPSManual.pdf"
get MD00082-2B-MIPS32INT-AFP-03.02.pdf "https://riteme.site/nscscc/doc/mips/Volume%20I:%20Introduction%20to%20MIPS32%20Architecture.pdf"
get MD00082-2B-MIPS32INT-AFP-00.95.pdf "https://www.ece.lsu.edu/ee4720/mips32v1.pdf"
sha256sum -c SHA256SUMS
command -v pdftotext >/dev/null && for f in *.pdf; do pdftotext -layout "$f" "${f%.pdf}.txt"; done

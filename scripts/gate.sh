#!/usr/bin/env bash
# gate.sh -- the single source of truth for "is this tree green".
#
#   scripts/gate.sh [--quick] [--from STEP | --only STEP] [--allow-warnings]
#                   [--fix] [--json] [--selftest] [-h]
#
# STEP is a number 1-10, a letter a-j, or a name (forbidden build check
# comparator diffharness equivharness oracle trace manuals hygiene).
# Only a FULL run (all 10 steps, none failed, tree unchanged during the run)
# writes the stamp .gate/green, whose tree id gate-commit.sh and the
# pre-commit hook compare against. See scripts/README.md.
#
# Environment (for tests / unusual layouts):
#   GATE_ROOT        repo root to verify (default: parent of this script)
#   GATE_DIR         state dir for logs/stamp (default: $GATE_ROOT/.gate)
#   GATE_CORPUS_DIR  where to count expected corpus programs
#                    (default: $GATE_ROOT/tests/corpus)
set -u
set -o pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=${GATE_ROOT:-$(cd "$SCRIPT_DIR/.." && pwd)}
GATE_DIR=${GATE_DIR:-$ROOT/.gate}
LOGDIR=$GATE_DIR/logs
CORPUS_DIR=${GATE_CORPUS_DIR:-$ROOT/tests/corpus}
ALLOW_FILE=$ROOT/scripts/gate-allow.txt
STD_AXIOMS="propext Classical.choice Quot.sound"
MARS_JAR=vendor/mars/Mars4_5.jar

STEP_NAMES=(forbidden build check comparator diffharness equivharness oracle trace manuals hygiene)
NSTEPS=${#STEP_NAMES[@]}

# ---------------------------------------------------------------- scanner ---
# Embedded python3 helper: strips comments/strings from Lean source and reports
# forbidden constructs found in CODE only. `scan FILE...` or `selftest`.
read -r -d '' PYSCAN <<'PY'
import re, sys, os

CONSTRUCTS = [
    ("sorry",          r"(?<![\w'])sorry(?![\w'])"),
    ("admit",          r"(?<![\w'])admit(?![\w'])"),
    ("native_decide",  r"(?<![\w'])native_decide(?![\w'])"),
    ("bv_decide",      r"(?<![\w'])bv_decide(?![\w'])"),
    ("axiom",          r"(?<![\w'.])axiom(?![\w'])"),
    ("partial def",    r"(?<![\w'])partial\s+def(?![\w'])"),
    ("unsafe",         r"(?<![\w'])unsafe(?![\w'])"),
    ("implemented_by", r"(?:@|attribute\s*)\[[^\]\n]*(?<![\w'])implemented_by(?![\w'])"),
    ("extern",         r"(?:@|attribute\s*)\[[^\]\n]*(?<![\w'])extern(?![\w'])"),
]
COMPILED = [(n, re.compile(p)) for n, p in CONSTRUCTS]
RAWSTR = re.compile(r'r(#*)"')
CHARLIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
IDCH = re.compile(r"[\w'!?]")

def blank(s):
    return re.sub(r"[^\n]", " ", s)

def strip(src):
    """Replace comments (line, nested block) and string/char literals by
    spaces, preserving newlines so line numbers survive."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2
            elif src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        prev = src[i - 1] if i else ""
        if c == "r" and not IDCH.match(prev or " "):
            m = RAWSTR.match(src, i)
            if m:
                close = '"' + m.group(1)
                j = src.find(close, m.end())
                j = n if j < 0 else j + len(close)
                out.append(blank(src[i:j])); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(blank(src[i:j])); i = j; continue
        if c == "'" and not IDCH.match(prev or " "):
            m = CHARLIT.match(src, i)
            if m:
                out.append(" " * (m.end() - i)); i = m.end(); continue
        out.append(c); i += 1
    return "".join(out)

def hits(src):
    res = []
    for ln, line in enumerate(strip(src).split("\n"), 1):
        for name, rx in COMPILED:
            if rx.search(line):
                res.append((ln, name))
    return res

def selftest():
    cases = [
        ("-- sorry in a line comment\n", []),
        ("/-- docstring mentioning sorry and native_decide -/\ntheorem x : True := trivial\n", []),
        ("/- outer /- inner sorry -/ still comment sorry -/\ndef x := 1\n", []),
        ('def s := "sorry -- not a comment, admit"\n', []),
        ('def s := "a\\"sorry"\n', []),
        ('def s := r#"sorry "quoted" bv_decide"#\n', []),
        ("theorem sorryAx_free : True := trivial\ndef my_sorry := 1\ndef sorry' := 2\n", []),
        ("#print axioms foo\n-- axiom foo : False\n", []),
        ("def y := 1 -- trailing sorry\n", []),
        ("theorem t : True := by sorry\n", [(1, "sorry")]),
        ('def s := "a"\nexample : True := by\n  sorry\n', [(3, "sorry")]),
        ("/- c -/ example : True := by sorry\n", [(1, "sorry")]),
        ("example : True := by\n  admit\n", [(2, "admit")]),
        ("example : 1 = 1 := by native_decide\n", [(1, "native_decide")]),
        ("example (x : BitVec 8) : x = x := by bv_decide\n", [(1, "bv_decide")]),
        ("example (x : BitVec 8) : x = x := by bv_decide?\n", [(1, "bv_decide")]),
        ("axiom foo : False\n", [(1, "axiom")]),
        ("private axiom foo : False\n", [(1, "axiom")]),
        ("partial def f (n : Nat) : Nat := f n\n", [(1, "partial def")]),
        ("unsafe def f := 1\n", [(1, "unsafe")]),
        ("@[implemented_by foo] def f := 1\n", [(1, "implemented_by")]),
        ('@[inline, extern "c_f"] def f := 1\n', [(1, "extern")]),
        # a char literal containing a double quote must not open a string
        ("def c := '\"'\nexample : True := by sorry\n", [(2, "sorry")]),
        # an apostrophe in an identifier is not a char literal
        ("def x' := 1\nexample : True := by sorry\n", [(2, "sorry")]),
        # `--` inside a string does not start a comment
        ('def s := "--"\nexample : True := by sorry\n', [(2, "sorry")]),
    ]
    bad = 0
    for k, (src, want) in enumerate(cases, 1):
        got = hits(src)
        ok = got == want
        bad += not ok
        print("%s case %2d: %-62r -> %s" % ("ok  " if ok else "FAIL", k, src[:60], got if ok else "got %s want %s" % (got, want)))
    print("scanner selftest: %d cases, %d failed" % (len(cases), bad))
    return 1 if bad else 0

def load_allow(path):
    allow, errs = set(), []
    if not os.path.exists(path):
        return allow, errs
    for k, raw in enumerate(open(path, encoding="utf-8"), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if "#" not in line:
            errs.append("%s:%d: allowlist entry needs a '# reason'" % (path, k)); continue
        ent = line.split("#", 1)[0].strip()
        if ":" not in ent:
            errs.append("%s:%d: expected path:construct" % (path, k)); continue
        p, c = ent.rsplit(":", 1)
        allow.add((p.strip(), c.strip()))
    return allow, errs

def scan(root, allow_path, files):
    allow, errs = load_allow(allow_path)
    for e in errs:
        print("ERROR " + e)
    bad, allowed = 0, 0
    for rel in files:
        with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as f:
            src = f.read()
        lines = src.split("\n")
        for ln, name in hits(src):
            if (rel, name) in allow:
                allowed += 1
                print("allowed: %s:%d: %s" % (rel, ln, name))
            else:
                bad += 1
                print("%s:%d: forbidden `%s`: %s" % (rel, ln, name, lines[ln - 1].strip()[:100]))
    print("scanned %d files; %d forbidden, %d allowlisted" % (len(files), bad, allowed))
    return 1 if (bad or errs) else 0

if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        sys.exit(selftest())
    sys.exit(scan(sys.argv[2], sys.argv[3], sys.argv[4:]))
PY

# ------------------------------------------------------------ small utils ---
die() { echo "gate: $*" >&2; exit 2; }

current_tree() {
  # Tree id of the exact working-tree content (honours .gitignore), computed
  # in a temporary copy of the index so the user's real index is untouched.
  local d idx real rc
  d=$(mktemp -d) || return 1
  idx=$d/index
  real=$(git -C "$ROOT" rev-parse --path-format=absolute --git-path index 2>/dev/null)
  [ -n "$real" ] && [ -f "$real" ] && cp "$real" "$idx"
  GIT_INDEX_FILE=$idx git -C "$ROOT" add -A -- . >/dev/null 2>&1 &&
    GIT_INDEX_FILE=$idx git -C "$ROOT" rm -r --cached -q --ignore-unmatch -- .gate >/dev/null 2>&1 &&
    GIT_INDEX_FILE=$idx git -C "$ROOT" write-tree
  rc=$?
  rm -rf "$d"
  return $rc
}

step_index() {  # resolve name/letter/number to 1-based index
  local s=${1,,} i
  case $s in
    [1-9]|10) echo "$s"; return 0 ;;
    [a-j]) echo $(( $(printf '%d' "'$s") - 96 )); return 0 ;;
  esac
  for i in "${!STEP_NAMES[@]}"; do
    [ "${STEP_NAMES[$i]}" = "$s" ] && { echo $((i + 1)); return 0; }
  done
  return 1
}

# ------------------------------------------------------------------ args ---
QUICK=0; FROM=""; ONLY=""; ALLOW_WARN=0; FIX=0; JSON_STDOUT=0
while [ $# -gt 0 ]; do
  case $1 in
    --quick) QUICK=1 ;;
    --from) shift; [ $# -gt 0 ] || die "--from needs a step"; FROM=$(step_index "$1") || die "unknown step: $1" ;;
    --only) shift; [ $# -gt 0 ] || die "--only needs a step"; ONLY=$(step_index "$1") || die "unknown step: $1" ;;
    --allow-warnings) ALLOW_WARN=1 ;;
    --fix) FIX=1 ;;
    --json) JSON_STDOUT=1 ;;
    --selftest) exec python3 -I -c "$PYSCAN" selftest ;;
    -h|--help) sed -n '2,19p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) die "unknown argument: $1 (try --help)" ;;
  esac
  shift
done
[ -n "$FROM" ] && [ -n "$ONLY" ] && die "--from and --only are exclusive"
[ -d "$ROOT" ] || die "GATE_ROOT not a directory: $ROOT"
cd "$ROOT" || die "cannot cd to $ROOT"
git rev-parse --git-dir >/dev/null 2>&1 || die "$ROOT is not a git repository"

declare -A SEL
for ((i = 1; i <= NSTEPS; i++)); do SEL[$i]=1; done
FULL=1
if [ $QUICK = 1 ]; then
  FULL=0; for i in 2 3 4 5 6 7; do SEL[$i]=0; done
elif [ -n "$ONLY" ]; then
  FULL=0; for ((i = 1; i <= NSTEPS; i++)); do SEL[$i]=0; done; SEL[$ONLY]=1
elif [ -n "$FROM" ]; then
  FULL=0; for ((i = 1; i < FROM; i++)); do SEL[$i]=0; done
fi

mkdir -p "$LOGDIR" || die "cannot create $LOGDIR"
[ $FULL = 1 ] && rm -f "$GATE_DIR/green"

# ------------------------------------------------------------ step bodies ---
NOTE=""
X_CORPUS=""; X_EQUIV=""; X_ORACLE=""; X_CONSTR=""; X_THEOREMS=""; X_AXIOMS=""; X_WARNINGS=""; X_COMPARATOR=""

step_forbidden() {
  local files=() f
  while IFS= read -r f; do files+=("$f"); done < <(
    { find Semantics -name '*.lean' -not -path '*/.lake/*' 2>/dev/null
      for f in Checked.lean Semantics.lean DiffHarness.lean EquivHarness.lean MipsRun.lean; do [ -f "$f" ] && echo "$f"; done; } | sort -u)
  [ ${#files[@]} -gt 0 ] || { echo "no Lean sources found under $ROOT"; return 1; }
  python3 -I -c "$PYSCAN" scan "$ROOT" "$ALLOW_FILE" "${files[@]}"
  local rc=$?
  NOTE="${#files[@]} files scanned"
  return $rc
}

step_build() {
  local log=$1
  lake build Semantics Checked DiffHarness EquivHarness MipsRun
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="lake build exit $rc"; return 1; }
  # Compiler warnings from project files (lake prints "warning: PATH:L:C: msg").
  local w
  w=$(grep -E '^warning: [^ ]+\.lean:[0-9]+:[0-9]+:' "$log" | grep -vE '^warning: (\./)?(\.lake/|/)|/\.lake/' || true)
  X_WARNINGS=$(printf '%s' "$w" | grep -c . || true)
  if [ "$X_WARNINGS" -gt 0 ]; then
    echo "---- $X_WARNINGS project warning(s) ----"
    printf '%s\n' "$w" | cut -c1-200
    if [ $ALLOW_WARN = 1 ]; then NOTE="$X_WARNINGS warnings (allowed by --allow-warnings)"; return 0; fi
    NOTE="$X_WARNINGS project compiler warning(s); fix them (or --allow-warnings if the owner agreed)"
    return 1
  fi
  NOTE="build ok, 0 project warnings"
}

step_check() {
  local log=$1
  lake check
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="lake check exit $rc"; return 1; }
  local line
  line=$(grep -m1 -E 'Uses axioms:' "$log" || true)
  [ -n "$line" ] || { NOTE="no 'Uses axioms:' line in lake check output"; return 1; }
  local list tok bad="" ok
  list=$(printf '%s' "${line#*Uses axioms:}" | tr -d '[],' )
  X_AXIOMS=""
  for tok in $list; do
    ok=0; for a in $STD_AXIOMS; do [ "$tok" = "$a" ] && ok=1; done
    [ $ok = 1 ] || bad="$bad $tok"
    X_AXIOMS="${X_AXIOMS:+$X_AXIOMS,}$tok"
  done
  [ -z "$bad" ] || { NOTE="non-standard axioms:$bad"; return 1; }
  NOTE="axioms: ${X_AXIOMS:-none}"
}

step_comparator() {
  local log=$1
  lake comparator
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="lake comparator exit $rc"; return 1; }
  grep -q 'Your solution is okay!' "$log" || { NOTE="'Your solution is okay!' missing from output"; return 1; }
  X_COMPARATOR=1
  NOTE="Your solution is okay!"
}

step_diffharness() {
  local log=$1
  command -v java >/dev/null 2>&1 || { echo "java not found on PATH; DiffHarness needs a JRE to run MARS"; NOTE="java missing"; return 1; }
  [ -f "$MARS_JAR" ] || { echo "$MARS_JAR missing; DiffHarness cannot run MARS"; NOTE="$MARS_JAR missing"; return 1; }
  local expected
  expected=$(find "$CORPUS_DIR" -maxdepth 1 -name '*.asm' 2>/dev/null | wc -l)
  lake exe DiffHarness
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="DiffHarness exit $rc"; return 1; }
  local n
  n=$(sed -n 's/.*SUMMARY: all \([0-9][0-9]*\) corpus programs PASS.*/\1/p' "$log" | tail -1)
  [ -n "$n" ] || { NOTE="no 'SUMMARY: all N corpus programs PASS' line"; return 1; }
  if [ "$n" != "$expected" ]; then
    echo "corpus size mismatch: harness reported $n, $CORPUS_DIR has $expected .asm files"
    NOTE="corpus mismatch: harness $n vs $expected files"; return 1
  fi
  X_CORPUS=$n
  NOTE="all $n corpus programs PASS vs MARS"
}

step_equivharness() {
  local log=$1
  lake exe EquivHarness
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="EquivHarness exit $rc"; return 1; }
  local n
  n=$(sed -n 's/.*SUMMARY: all \([0-9][0-9]*\) equivalence cases behaved as claimed.*/\1/p' "$log" | tail -1)
  [ -n "$n" ] || { NOTE="no 'SUMMARY: all N equivalence cases' line"; return 1; }
  X_EQUIV=$n
  NOTE="$n equivalence cases behaved as claimed"
}

# QEMU/LLVM differential oracle (scripts/oracle.py): behaviour suite (+ tests/asm), encodings vs llvm-mc, harness selftest.
# Missing qemu-system-mips / LLVM tools is a FAIL, never a skip. Declared QEMU deviations and known model bugs do not fail the
# step (they are counted and printed); any undeclared mismatch, stale declaration or harness error does.
step_oracle() {
  local log=$1 rc st sm
  python3 scripts/oracle.py selftest
  rc=$?
  [ $rc -eq 0 ] || { NOTE="oracle selftest failed (exit $rc; 2 = qemu/llvm missing)"; return 1; }
  echo "=== oracle behaviour suite (+ tests/asm)"
  python3 scripts/oracle.py --asm
  rc=$?
  [ $rc -eq 0 ] || { NOTE="oracle behaviour suite failed (exit $rc; 2 = qemu/llvm missing)"; return 1; }
  echo "=== oracle encodings vs llvm-mc"
  python3 scripts/oracle.py --encodings
  rc=$?
  [ $rc -eq 0 ] || { NOTE="oracle encodings failed (exit $rc; 2 = qemu/llvm missing)"; return 1; }
  st=$(grep -E '^SUMMARY: [0-9]+ tests' "$log" | tail -1)
  sm=$(grep -E '^ENCODINGS: ' "$log" | tail -1)
  [ -n "$st" ] && [ -n "$sm" ] || { NOTE="no oracle SUMMARY/ENCODINGS line"; return 1; }
  local n p d k f sk
  n=$(echo "$st" | sed -n 's/^SUMMARY: \([0-9]*\) tests.*/\1/p')
  p=$(echo "$st" | sed -n 's/.* \([0-9]*\) pass.*/\1/p')
  d=$(echo "$st" | sed -n 's/.* \([0-9]*\) declared deviations.*/\1/p')
  k=$(echo "$st" | sed -n 's/.* \([0-9]*\) known model bugs.*/\1/p')
  f=$(echo "$st" | sed -n 's/.* \([0-9]*\) fail.*/\1/p')
  sk=$(echo "$st" | sed -n 's/.* \([0-9]*\) skipped.*/\1/p')
  [ "$f" = 0 ] || { NOTE="oracle: $f failing tests"; return 1; }
  [ $((p + d + k)) -eq "$n" ] || { NOTE="oracle: counts do not add up ($st)"; return 1; }
  local es ed
  es=$(echo "$sm" | sed -n 's/.* \([0-9]*\) same.*/\1/p'); ed=$(echo "$sm" | sed -n 's/.* \([0-9]*\) declared.*/\1/p')
  X_ORACLE=$n
  NOTE="$n tests: $p pass, $d declared QEMU deviations, $k known model bugs, $sk skipped; encodings $es same, $ed declared"
}

step_trace() {
  local log=$1 tmp rc
  [ -f scripts/trace.py ] || { echo "scripts/trace.py missing"; NOTE="trace.py missing"; return 1; }
  # --out always goes to a temp file so a check never rewrites docs/TRACE.md.
  tmp=$(mktemp)
  python3 scripts/trace.py --check --out "$tmp"
  rc=$?
  X_CONSTR=$(sed -n 's/^constructors: \([0-9]*\).*/\1/p' "$log" | head -1)
  X_THEOREMS=$(sed -n 's/^spec theorems.*: \([0-9]*\) \/ [0-9]*.*/\1/p' "$log" | head -1)
  if [ $rc -ne 0 ]; then rm -f "$tmp"; NOTE="trace.py --check failed (missing step arm / spec theorem / sorry)"; return 1; fi
  if [ ! -f docs/TRACE.md ]; then rm -f "$tmp"; echo "docs/TRACE.md missing; run: python3 scripts/trace.py"; NOTE="docs/TRACE.md missing"; return 1; fi
  if diff <(grep -v '^- git HEAD:' docs/TRACE.md) <(grep -v '^- git HEAD:' "$tmp") >"$log.diff"; then
    rm -f "$tmp" "$log.diff"
    NOTE="${X_CONSTR:-?} constructors, ${X_THEOREMS:-?} spec theorems, TRACE.md current"
    return 0
  fi
  head -12 "$log.diff" | cut -c1-160; rm -f "$tmp"
  echo "docs/TRACE.md is stale: run 'python3 scripts/trace.py' (or gate.sh --fix) and include it"
  NOTE="docs/TRACE.md out of date"
  return 1
}

step_manuals() {
  local log=$1
  [ -f docs/spec/manuals/mipsdoc.py ] || { NOTE="mipsdoc.py missing"; return 1; }
  python3 docs/spec/manuals/mipsdoc.py selftest
  local rc=$?
  [ $rc -eq 0 ] || { NOTE="mipsdoc.py selftest exit $rc"; return 1; }
  if grep -q '^SKIP:' "$log"; then NOTE="manual texts absent (run docs/spec/manuals/fetch.sh)"; return 2; fi
  NOTE="$(tail -1 "$log")"
}

step_hygiene() {
  local fail=0 f sz n
  # shellcheck disable=SC2155
  local list; list=$(mktemp)
  git ls-files -z --cached --others --exclude-standard | sort -zu > "$list"
  # 1. merge-conflict markers (at line start) in text files
  xargs -0 -a "$list" grep -I -s -n -E '^(<{7} |>{7} )' 2>/dev/null | head -20 > "$list.cm"
  if [ -s "$list.cm" ]; then echo "merge-conflict markers:"; cat "$list.cm"; fail=1; fi
  # 2. files > 5 MB
  while IFS= read -r -d '' f; do
    [ -f "$f" ] || continue
    sz=$(stat -c %s "$f"); [ "$sz" -gt 5242880 ] && { echo "file > 5 MB: $f ($sz bytes)"; fail=1; }
  done < "$list"
  # 3. PDFs staged or untracked-unignored
  while IFS= read -r -d '' f; do
    case ${f,,} in *.pdf) echo "pdf would be committed: $f"; fail=1 ;; esac
  done < "$list"
  # 4. whitespace errors: warning only
  n=$(git diff --check HEAD 2>/dev/null | grep -c . || true)
  [ "$n" -gt 0 ] && echo "warning: git diff --check reports $n whitespace issue(s) (not a failure)"
  rm -f "$list" "$list.cm"
  if [ $fail = 1 ]; then NOTE="hygiene violations (see log)"; return 1; fi
  NOTE="no conflict markers, no >5MB files, no pdfs; whitespace warnings: $n"
  return 0
}

# ------------------------------------------------------------------ driver ---
if [ $FULL = 0 ]; then
  echo "== gate: PARTIAL run (--quick/--from/--only). This is NOT a green gate; no stamp will be written. =="
fi
[ $FIX = 1 ] && [ "${SEL[8]}" = 1 ] && {
  python3 scripts/trace.py > "$LOGDIR/00-fix-trace.log" 2>&1 \
    && echo "gate: --fix regenerated docs/TRACE.md" || echo "gate: --fix: trace.py failed, see $LOGDIR/00-fix-trace.log"
}
TREE0=$(current_tree) || TREE0=""
declare -a RES SECS NOTES
ANY_FAIL=0; ANY_RUN=0
t_all=$SECONDS
for ((i = 1; i <= NSTEPS; i++)); do
  name=${STEP_NAMES[$((i - 1))]}
  if [ "${SEL[$i]}" != 1 ]; then RES[$i]=NOTRUN; SECS[$i]=0; NOTES[$i]=""; continue; fi
  ANY_RUN=1
  log=$LOGDIR/$(printf '%02d' "$i")-$name.log
  printf '[%d/%d] %-14s ... ' "$i" "$NSTEPS" "$name"
  NOTE=""; t0=$SECONDS
  "step_$name" "$log" >"$log" 2>&1
  rc=$?
  SECS[$i]=$((SECONDS - t0)); NOTES[$i]=$NOTE
  case $rc in
    0) RES[$i]=PASS ;;
    2) RES[$i]=SKIP ;;
    *) RES[$i]=FAIL; ANY_FAIL=1 ;;
  esac
  printf '%s (%ss)' "${RES[$i]}" "${SECS[$i]}"
  [ -n "$NOTE" ] && printf '  %s' "$NOTE"
  printf '\n'
  if [ "${RES[$i]}" = FAIL ]; then
    echo "    ---- last 40 lines of $log ----"
    tail -n 40 "$log" | sed 's/^/    | /'
  fi
done

TREE1=$(current_tree) || TREE1=""
STAMPED=0; VERDICT=
if [ $ANY_FAIL = 1 ]; then VERDICT="RED"
elif [ $FULL = 0 ]; then VERDICT="PARTIAL-PASS (not a green gate)"
elif [ -z "$TREE1" ] || [ "$TREE0" != "$TREE1" ]; then
  VERDICT="RED (the working tree changed while the gate ran; re-run)"; ANY_FAIL=1
else
  VERDICT="GREEN"; STAMPED=1
fi

# ------------------------------------------------------------ stamp + json ---
TOOLCHAIN=$( (cd "$ROOT" && lean --version) 2>/dev/null | head -1); TOOLCHAIN=${TOOLCHAIN:-unknown}
HEADREV=$(git rev-parse HEAD 2>/dev/null || echo none)
NOW=$(date -u +%Y-%m-%dT%H:%M:%SZ)
if [ $STAMPED = 1 ]; then
  {
    echo "tree=$TREE1"
    echo "timestamp=$NOW"
    echo "head=$HEADREV"
    echo "toolchain=$TOOLCHAIN"
    echo "allow_warnings=$ALLOW_WARN"
    for ((i = 1; i <= NSTEPS; i++)); do echo "step.${STEP_NAMES[$((i - 1))]}=${RES[$i]}"; done
    echo "corpus=$X_CORPUS"; echo "equiv=$X_EQUIV"; echo "oracle=$X_ORACLE"
    echo "constructors=$X_CONSTR"; echo "theorems=$X_THEOREMS"
    echo "axioms=$X_AXIOMS"; echo "warnings=${X_WARNINGS:-0}"
  } > "$GATE_DIR/green"
fi

TSV=$(mktemp)
for ((i = 1; i <= NSTEPS; i++)); do
  printf '%s\t%s\t%s\t%s\t%s\n' "$i" "${STEP_NAMES[$((i - 1))]}" "${RES[$i]}" "${SECS[$i]}" "${NOTES[$i]}" >> "$TSV"
done
VERDICT="$VERDICT" STAMPED=$STAMPED FULLRUN=$FULL NOW=$NOW HEADREV=$HEADREV TREE="$TREE1" \
CORPUS=$X_CORPUS EQUIV=$X_EQUIV ORACLE=$X_ORACLE CONSTR=$X_CONSTR THEOREMS=$X_THEOREMS AXIOMS=$X_AXIOMS \
WARNINGS=${X_WARNINGS:-0} TOOLCHAIN="$TOOLCHAIN" TOTAL=$((SECONDS - t_all)) \
python3 -I - "$TSV" "$GATE_DIR/last-run.json" <<'PY'
import json, os, sys
e = os.environ
steps = []
for line in open(sys.argv[1], encoding="utf-8"):
    n, name, st, secs, note = (line.rstrip("\n").split("\t") + [""] * 5)[:5]
    steps.append({"n": int(n), "name": name, "status": st, "seconds": int(secs), "note": note})
def num(k):
    return int(e[k]) if e.get(k, "").isdigit() else None
doc = {"verdict": e["VERDICT"], "full_run": e["FULLRUN"] == "1", "stamped": e["STAMPED"] == "1",
       "timestamp": e["NOW"], "head": e["HEADREV"], "tree": e["TREE"] or None,
       "toolchain": e["TOOLCHAIN"], "total_seconds": int(e["TOTAL"]), "steps": steps,
       "corpus": num("CORPUS"), "equiv": num("EQUIV"), "oracle": num("ORACLE"), "constructors": num("CONSTR"),
       "theorems": num("THEOREMS"), "warnings": num("WARNINGS"),
       "axioms": [a for a in e["AXIOMS"].split(",") if a]}
json.dump(doc, open(sys.argv[2], "w"), indent=2); open(sys.argv[2], "a").write("\n")
PY
rm -f "$TSV"
[ $JSON_STDOUT = 1 ] && cat "$GATE_DIR/last-run.json"

echo "== gate: $VERDICT ($((SECONDS - t_all))s). Logs: $LOGDIR; summary: $GATE_DIR/last-run.json =="
if [ $STAMPED = 1 ]; then
  echo "== stamp written: $GATE_DIR/green (tree $TREE1). Commit with: scripts/gate-commit.sh \"<subject>\" =="
elif [ $FULL = 1 ] && [ $ANY_FAIL = 0 ]; then :
fi
[ $ANY_FAIL = 0 ] && exit 0
exit 1

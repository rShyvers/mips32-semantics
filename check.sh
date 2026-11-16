#!/usr/bin/env bash
# check.sh -- is this docs branch in step with the code it describes?  See README.md.
#   ./check.sh          check (exit 0 = in step)
#   ./check.sh --fix    regenerate TRACE.md, then check
#   ./check.sh --sync   record the code HEAD in SYNC (only if TRACE.md and the compliance check pass)
set -u
DOCS=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$DOCS")
if [ ! -f "$ROOT/lakefile.toml" ] || [ ! -f "$ROOT/scripts/trace.py" ]; then
  echo "check.sh: mount this branch at <code checkout>/docs (git worktree add docs documentation)"; exit 2
fi
mode=${1:-}
fail=0
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT

if [ "$mode" = --fix ]; then
  python3 "$ROOT/scripts/trace.py" --out "$DOCS/TRACE.md" >/dev/null || { echo "trace.py failed"; exit 1; }
fi

# 1. TRACE.md is current (the git-HEAD line is ignored).
if python3 "$ROOT/scripts/trace.py" --out "$tmp" >/dev/null &&
   diff <(grep -v '^- git HEAD:' "$DOCS/TRACE.md") <(grep -v '^- git HEAD:' "$tmp") >/dev/null; then
  echo "ok    TRACE.md current"
else
  echo "FAIL  TRACE.md stale: ./check.sh --fix"; fail=1
fi

# 2. The compliance matrix covers every register field / instruction of the manuals.
if python3 "$DOCS/tools/compliance.py" check >"$tmp" 2>&1; then
  echo "ok    compliance: $(tail -1 "$tmp")"
else
  sed 's/^/      /' "$tmp" | tail -15; echo "FAIL  compliance check"; fail=1
fi

head=$(git -C "$ROOT" rev-parse HEAD)
if [ "$mode" = --sync ]; then
  [ $fail -eq 0 ] || { echo "not syncing: fix the failures above"; exit 1; }
  echo "$head" > "$DOCS/SYNC"; echo "SYNC <- $head"; exit 0
fi

# 3. No code change since the commit these docs describe.
described=$(tr -d '[:space:]' < "$DOCS/SYNC")
if ! git -C "$ROOT" cat-file -e "$described^{commit}" 2>/dev/null; then
  echo "FAIL  SYNC names unknown commit $described"; fail=1
else
  changed=$(git -C "$ROOT" diff --name-only "$described" "$head" -- Semantics tests scripts '*.lean' lakefile.toml comparator.json)
  if [ -n "$changed" ]; then
    echo "FAIL  code changed since SYNC ($described):"; echo "$changed" | head -20 | sed 's/^/      /'
    echo "      update the docs, then ./check.sh --sync"; fail=1
  else
    echo "ok    describes code at $described (HEAD $head)"
  fi
fi
exit $fail

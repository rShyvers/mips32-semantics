#!/usr/bin/env bash
# gate-commit.sh -- the ONLY sanctioned way to commit: commits exactly the tree
# that a full green `scripts/gate.sh` run verified. Never pushes.
#
#   scripts/gate-commit.sh [--run] "<subject>" [body-file]
#
#   --run   run scripts/gate.sh (full) first; abort if it is not green.
#
# Refuses when: on main/master (or detached HEAD); no .gate/green stamp; the
# current working-tree id differs from the stamp (something changed after the
# gate ran); nothing to commit. Env: GATE_ROOT, GATE_DIR as in gate.sh.
set -u
set -o pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=${GATE_ROOT:-$(cd "$SCRIPT_DIR/.." && pwd)}
GATE_DIR=${GATE_DIR:-$ROOT/.gate}
STAMP=$GATE_DIR/green
CO_AUTHOR='Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>'

die() { echo "gate-commit: REFUSED: $*" >&2; exit 1; }

RUN=0; SUBJECT=""; BODY=""
while [ $# -gt 0 ]; do
  case $1 in
    --run) RUN=1 ;;
    -h|--help) sed -n '2,12p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) if [ -z "$SUBJECT" ]; then SUBJECT=$1; elif [ -z "$BODY" ]; then BODY=$1; else die "too many arguments"; fi ;;
  esac
  shift
done
[ -n "$SUBJECT" ] || die "usage: gate-commit.sh [--run] \"<subject>\" [body-file]"
[ -z "$BODY" ] || [ -f "$BODY" ] || die "body file not found: $BODY"
cd "$ROOT" 2>/dev/null || die "cannot cd to $ROOT"
git rev-parse --git-dir >/dev/null 2>&1 || die "$ROOT is not a git repository"

BRANCH=$(git symbolic-ref --short -q HEAD) || die "detached HEAD; check out a dev branch first"
case $BRANCH in main|master) die "on '$BRANCH'; never commit there. Create a dev branch (git switch -c dev/...)" ;; esac

if [ $RUN = 1 ]; then
  "$SCRIPT_DIR/gate.sh" || die "gate is not green; nothing committed"
fi

[ -f "$STAMP" ] || die "no gate stamp ($STAMP). Run scripts/gate.sh (full) first, or use --run"
stamp_get() { sed -n "s/^$1=//p" "$STAMP" | head -1; }
STAMP_TREE=$(stamp_get tree)
[ -n "$STAMP_TREE" ] || die "stamp has no tree id; re-run scripts/gate.sh"

current_tree() {
  local d idx real rc
  d=$(mktemp -d) || return 1
  idx=$d/index
  real=$(git rev-parse --path-format=absolute --git-path index 2>/dev/null)
  [ -n "$real" ] && [ -f "$real" ] && cp "$real" "$idx"
  GIT_INDEX_FILE=$idx git add -A -- . >/dev/null 2>&1 &&
    GIT_INDEX_FILE=$idx git rm -r --cached -q --ignore-unmatch -- .gate >/dev/null 2>&1 &&
    GIT_INDEX_FILE=$idx git write-tree
  rc=$?
  rm -rf "$d"
  return $rc
}

NOW_TREE=$(current_tree) || die "cannot compute the current tree id"
if [ "$NOW_TREE" != "$STAMP_TREE" ]; then
  die "stale stamp: the working tree changed after the gate ran (stamp $STAMP_TREE, now $NOW_TREE). Re-run scripts/gate.sh"
fi
HEAD_TREE=$(git rev-parse 'HEAD^{tree}' 2>/dev/null || echo none)
[ "$NOW_TREE" != "$HEAD_TREE" ] || die "nothing to commit (tree identical to HEAD)"

# Compose the message.
MSG=$(mktemp)
SAVED_INDEX=$(mktemp)
trap 'rm -f "$MSG" "$SAVED_INDEX"' EXIT
{
  printf '%s\n' "$SUBJECT"
  if [ -n "$BODY" ]; then printf '\n'; cat "$BODY"; fi
  printf '\n'
  printf 'Gate: green (tree %s, %s)\n' "$STAMP_TREE" "$(stamp_get timestamp)"
  printf 'Gate-Steps: forbidden=%s build=%s check=%s comparator=%s diffharness=%s equivharness=%s oracle=%s trace=%s manuals=%s hygiene=%s\n' \
    "$(stamp_get step.forbidden)" "$(stamp_get step.build)" "$(stamp_get step.check)" "$(stamp_get step.comparator)" \
    "$(stamp_get step.diffharness)" "$(stamp_get step.equivharness)" "$(stamp_get step.oracle)" "$(stamp_get step.trace)" "$(stamp_get step.manuals)" "$(stamp_get step.hygiene)"
  printf 'Gate-Corpus: %s programs PASS vs MARS\n' "$(stamp_get corpus)"
  printf 'Gate-Equiv: %s cases\n' "$(stamp_get equiv)"
  printf 'Gate-Oracle: %s QEMU/LLVM oracle tests\n' "$(stamp_get oracle)"
  printf 'Gate-Trace: %s constructors, %s spec theorems\n' "$(stamp_get constructors)" "$(stamp_get theorems)"
  printf 'Gate-Axioms: %s\n' "$(stamp_get axioms)"
  printf 'Gate-Warnings: %s (allow_warnings=%s)\n' "$(stamp_get warnings)" "$(stamp_get allow_warnings)"
  printf 'Gate-Toolchain: %s\n' "$(stamp_get toolchain | cut -c1-80)"
  printf '%s\n' "$CO_AUTHOR"
} > "$MSG"

REAL_INDEX=$(git rev-parse --path-format=absolute --git-path index)
[ -f "$REAL_INDEX" ] && cp "$REAL_INDEX" "$SAVED_INDEX" || : > "$SAVED_INDEX"
HAD_INDEX=0; [ -f "$REAL_INDEX" ] && HAD_INDEX=1

git add -A -- . || die "git add -A failed"
git rm -r --cached -q --ignore-unmatch -- .gate >/dev/null 2>&1
STAGED=$(git write-tree) || { [ $HAD_INDEX = 1 ] && cp "$SAVED_INDEX" "$REAL_INDEX"; die "git write-tree failed"; }
if [ "$STAGED" != "$STAMP_TREE" ]; then
  [ $HAD_INDEX = 1 ] && cp "$SAVED_INDEX" "$REAL_INDEX"
  die "staged tree $STAGED differs from stamped tree $STAMP_TREE (index restored). Re-run scripts/gate.sh"
fi

if ! git commit -q -F "$MSG"; then
  echo "gate-commit: git commit failed (pre-commit hook?). Index left staged; nothing pushed." >&2
  exit 1
fi
echo "gate-commit: committed $(git rev-parse --short HEAD) on $BRANCH (tree $STAMP_TREE). Not pushed."
git rev-parse HEAD

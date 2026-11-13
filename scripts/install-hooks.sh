#!/usr/bin/env bash
# install-hooks.sh -- enable the repo's .githooks/ for THIS clone only
# (git config --local core.hooksPath .githooks). Idempotent.
set -eu
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=${GATE_ROOT:-$(cd "$SCRIPT_DIR/.." && pwd)}
[ -f "$ROOT/.githooks/pre-commit" ] || { echo "install-hooks: $ROOT/.githooks/pre-commit missing" >&2; exit 1; }
chmod +x "$ROOT/.githooks/pre-commit"
cur=$(git -C "$ROOT" config --local --get core.hooksPath || true)
if [ "$cur" = ".githooks" ]; then
  echo "install-hooks: already installed (core.hooksPath=.githooks)"
else
  git -C "$ROOT" config --local core.hooksPath .githooks
  echo "install-hooks: core.hooksPath set to .githooks (was: ${cur:-unset}) for this clone"
fi
echo "Commits now require a green gate stamp. Bypass in an emergency: git commit --no-verify"

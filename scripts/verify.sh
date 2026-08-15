#!/usr/bin/env bash
# Local verification cadence: lake build and a sorry-free scan.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

lake build

if command -v rg >/dev/null 2>&1; then
  if rg -n sorry --glob '*.lean' --glob '!.lake/**'; then
    echo "sorry found in Lean sources" >&2
    exit 1
  fi
else
  if grep -nR --include='*.lean' --exclude-dir=.lake 'sorry' .; then
    echo "sorry found in Lean sources" >&2
    exit 1
  fi
fi

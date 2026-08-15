#!/usr/bin/env bash
# Idempotent Cloud Agent install script for the NystromSubmodularity
# Lean 4 + mathlib4 project. Safe to run repeatedly.
set -euo pipefail

# Resolve the repository root (parent of this .cursor/ directory).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

# 1. Install elan (the Lean version manager) if it is not already present.
#    `--default-toolchain none` avoids pulling a toolchain we don't need;
#    the pinned `lean-toolchain` file selects the correct one on first use.
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

# 2. Materialize dependencies (pinned by lake-manifest.json), download
#    mathlib's prebuilt build cache, then build the project. Downloading the
#    cache avoids recompiling mathlib from source (which would take hours).
lake exe cache get
lake build

# 3. Python extras for graphnystrom tests. `--user` keeps the install
#    inside the agent home; safe to re-run.
if command -v python3 >/dev/null 2>&1; then
  python3 -m pip install --user -q 'numpy>=1.24' 'scipy>=1.11' 'pytest>=7.0'
fi

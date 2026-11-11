#!/usr/bin/env bash
# Run scripts/extract.mjs with the pinned Rust toolchain.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
node scripts/extract.mjs "$@"

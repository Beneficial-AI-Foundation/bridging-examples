#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
python3 scripts/check-pins.py --lean-only
for manifest in rust/*/Cargo.toml; do
  cargo check --offline --locked --manifest-path "$manifest"
done
node scripts/export.mjs
node scripts/verso.mjs
node browser/build.mjs
node browser/build.mjs --check

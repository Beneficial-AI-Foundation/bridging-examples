#!/usr/bin/env bash
# Check everything: the pins, each Rust crate, the Lean build and its audit, and the explorer.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
python3 scripts/check-pins.py --lean-only
for manifest in BridgingExamples/*/rust/Cargo.toml; do
  cargo check --offline --locked --manifest-path "$manifest"
done
node explorer/export.mjs
node explorer/verso.mjs
node explorer/build.mjs
node explorer/build.mjs --check

#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
mkdir -p .tools/llbc Generated
test "$(aeneas -version)" = 'aeneas nightly-2026.10.26-da2b22e'
test "$(charon version)" = '0.1.299 (40ca4ab6c10ecb7629320d6eccc0f41423fbe889)'
charon cargo --preset aeneas --sysroot default \
  --dest-file "$BRIDGE_ROOT/.tools/llbc/bridge_smoke.llbc" \
  -- --manifest-path "$BRIDGE_ROOT/rust/smoke/Cargo.toml"
aeneas -backend lean -dest "$BRIDGE_ROOT" -subdir Generated \
  -namespace bridge_smoke -split-files -emit-json -no-progress-bar \
  "$BRIDGE_ROOT/.tools/llbc/bridge_smoke.llbc"

#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
mkdir -p .tools/llbc Generated
test "$(aeneas -version)" = 'aeneas nightly-2026.08.27-5b9dcf3'
test "$(charon version)" = '0.1.245 (4ad295c1bf982b5533ce7d85f4ddc889ff3127f8)'
charon cargo --preset aeneas --sysroot default \
  --dest-file "$BRIDGE_ROOT/.tools/llbc/bridge_smoke.llbc" \
  -- --manifest-path "$BRIDGE_ROOT/rust/smoke/Cargo.toml"
aeneas -backend lean -dest "$BRIDGE_ROOT" -subdir Generated \
  -namespace bridge_smoke -split-files -emit-json -no-progress-bar \
  "$BRIDGE_ROOT/.tools/llbc/bridge_smoke.llbc"

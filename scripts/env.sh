#!/usr/bin/env bash
# Source this file to select the project's isolated Rust extraction toolchain.
BRIDGE_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="$BRIDGE_ROOT/.tools/rustup"
export CARGO_HOME="$BRIDGE_ROOT/.tools/cargo"
export PATH="$BRIDGE_ROOT/.tools/cargo/bin:$BRIDGE_ROOT/.tools/aeneas:$PATH"
export RUSTUP_TOOLCHAIN=nightly-2026-09-17
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

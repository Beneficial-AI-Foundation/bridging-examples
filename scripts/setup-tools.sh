#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"

# These assets and SHA-256 digests belong to the pinned GitHub release below.
# Keep the Rust host target aligned with the extraction binaries.
tag=nightly-2026.10.26-da2b22e
case "$(uname -s)/$(uname -m)" in
  Linux/x86_64)
    asset=aeneas-linux-x86_64.tar.gz
    digest=5ee16f90e4e2594351f3db7d248e31d87e6cf1c6918ca9658bfa3664d0f9c1a3
    rust_host=x86_64-unknown-linux-gnu
    ;;
  Linux/aarch64|Linux/arm64)
    asset=aeneas-linux-aarch64.tar.gz
    digest=441c7e5c0c26b100e8eb8ef39f4ea8d292446762a0e1a3cb2dc7742cbcafcdcc
    rust_host=aarch64-unknown-linux-gnu
    ;;
  Darwin/arm64|Darwin/aarch64)
    asset=aeneas-macos-aarch64.tar.gz
    digest=c118da207514dfb42cedeb36da60c9a34986004bf94a609aec2619da443060f3
    rust_host=aarch64-apple-darwin
    ;;
  *)
    echo 'No pinned extraction binary bundle is configured for this OS/architecture.' >&2
    echo 'Supported: Linux x86_64/ARM64 and Apple Silicon macOS (native ARM64 shell).' >&2
    echo 'Windows: run this script inside WSL2 Linux, not PowerShell or Git Bash.' >&2
    echo 'Intel Mac: use a supported Linux environment, or check the existing Lean proofs only.' >&2
    exit 1
    ;;
esac

# Read-only diagnostic, also usable before installing any tools.
if [[ "${1:-}" == --print-platform && "$#" -eq 1 ]]; then
  printf 'asset=%s\nrust_host=%s\nsha256=%s\n' "$asset" "$rust_host" "$digest"
  exit 0
fi
if [[ "$#" -ne 0 ]]; then
  echo 'Usage: bash scripts/setup-tools.sh [--print-platform]' >&2
  exit 1
fi
archive="$BRIDGE_ROOT/.tools/downloads/$tag/$asset"
mkdir -p ".tools/downloads/$tag" .tools/aeneas
if [[ ! -f "$archive" ]]; then
  curl -fLsS --retry 3 \
    "https://github.com/AeneasVerif/aeneas/releases/download/$tag/$asset" \
    -o "$archive"
fi
# Python is already needed by check-pins.py and avoids GNU-only sha256sum on macOS.
python3 - "$archive" "$digest" <<'PYHASH'
import hashlib
import sys

with open(sys.argv[1], "rb") as archive:
    actual = hashlib.sha256()
    for block in iter(lambda: archive.read(1024 * 1024), b""):
        actual.update(block)
if actual.hexdigest() != sys.argv[2]:
    raise SystemExit("Extraction archive SHA-256 mismatch: " + sys.argv[1])
print("Extraction archive SHA-256 verified.")
PYHASH
tar -xzf "$archive" -C .tools/aeneas
test "$(aeneas -version)" = "aeneas $tag"
test "$(charon version)" = '0.1.299 (40ca4ab6c10ecb7629320d6eccc0f41423fbe889)'
test "$(charon toolchain-version)" = "$RUSTUP_TOOLCHAIN"

if [[ ! -x "$CARGO_HOME/bin/rustup" ]]; then
  curl -fLsS --retry 3 \
    "https://static.rust-lang.org/rustup/dist/$rust_host/rustup-init" \
    -o ".tools/downloads/rustup-init-$rust_host"
  chmod +x ".tools/downloads/rustup-init-$rust_host"
  RUSTUP_INIT_SKIP_PATH_CHECK=yes ".tools/downloads/rustup-init-$rust_host" \
    -y --no-modify-path --profile minimal --default-toolchain none
fi
rustup toolchain install "$RUSTUP_TOOLCHAIN" --profile minimal \
  --component rustc-dev --component rust-src

echo 'Pinned extraction tools ready. Lean is selected by lean-toolchain.'

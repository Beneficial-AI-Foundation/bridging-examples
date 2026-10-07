#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$BRIDGE_ROOT"
nice -n 19 lake exe cache get
python3 scripts/check-pins.py
bash scripts/extract-smoke.sh
nice -n 19 lake build

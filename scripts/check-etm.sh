#!/usr/bin/env bash
set -euo pipefail
bash "$(dirname -- "${BASH_SOURCE[0]}")/extract-etm.sh"
bash "$(dirname -- "${BASH_SOURCE[0]}")/check-explorer.sh"
